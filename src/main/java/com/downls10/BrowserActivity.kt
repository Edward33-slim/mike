package com.downls10

import android.Manifest
import android.app.Activity
import android.app.AlertDialog
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Color
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.Parcel
import android.util.Patterns
import android.util.Base64
import android.view.Gravity
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
import android.view.inputmethod.EditorInfo
import android.webkit.CookieManager
import android.webkit.GeolocationPermissions
import android.webkit.PermissionRequest
import android.webkit.ValueCallback
import android.webkit.WebResourceRequest
import android.webkit.WebResourceResponse
import android.webkit.WebSettings
import android.webkit.WebView
import android.webkit.WebViewClient
import android.webkit.WebChromeClient
import android.widget.Button
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.GridLayout
import android.widget.ImageView
import android.widget.LinearLayout
import android.widget.ProgressBar
import android.widget.ScrollView
import android.widget.TextView
import android.widget.Toast
import java.io.File
import java.net.HttpURLConnection
import java.net.URL
import java.util.concurrent.Executors
import java.util.Locale
import org.json.JSONObject
import kotlin.math.abs

private data class Tab(
    val id: Long,
    val webView: WebView,
    var isHome: Boolean = true,
    var title: String = "صفحة جديدة",
    var desktopMode: Boolean = false,
    // Translation stays enabled for this tab while the user browses.
    var translationEnabled: Boolean = false,
    var translationInProgress: Boolean = false,
    var lastTranslatedUrl: String = "",
    val backStack: MutableList<String> = mutableListOf(),
    val forwardStack: MutableList<String> = mutableListOf(),
    // --- حفظ واستعادة موضع التمرير عند الرجوع/التقدم ---
    /** آخر موضع تمرير (بالبكسل) لكل رابط زاره هذا التبويب */
    val scrollPositions: MutableMap<String, Int> = mutableMapOf(),
    /** true أثناء تحميل صفحة جديدة (لا نسجّل التمرير حينها لأن الصفحة تبدأ من الصفر) */
    var pageLoading: Boolean = false,
    /** الموضع المطلوب استعادته الآن، أو -1 إذا لا توجد استعادة جارية */
    var pendingRestoreY: Int = -1,
    /** رقم يزيد عند بدء/إلغاء كل استعادة لإيقاف المحاولات القديمة */
    var restoreGeneration: Int = 0
)

class BrowserActivity : Activity() {

    companion object {
        const val EXTRA_OPEN_URL = "extra_open_url"
        private const val SEARCH_PROVIDER_KEY = "searchProvider"
        private const val SEARCH_SEARXNG = "searxng"
        private const val SEARCH_GOOGLE = "google"
        private const val SEARCH_METAGER = "metager"
        private const val SEARCH_4GET = "4get"
        private const val SEARCH_LIBREY = "librey"
        private const val SEARCH_MOJEEK = "mojeek"
        private const val SEARCH_BRAVE = "brave"
        private const val SEARCH_YACY = "yacy"
        private const val SEARCH_BING = "bing"
        private const val SEARCH_VIDEO = "video"
        private const val SEARXNG_SEARCH_BASE = "https://searx.ononoki.org/search?q="
        private const val METAGER_SEARCH_BASE = "https://metager.org/meta/meta.ger3?eingabe="
        private const val FOURGET_SEARCH_BASE = "https://4get.ca/web?s="
        private const val LIBREY_SEARCH_BASE = "https://librey.org/search.php?q="
        private const val MOJEEK_SEARCH_BASE = "https://www.mojeek.com/search?q="
        private const val BRAVE_SEARCH_BASE = "https://search.brave.com/search?q="
        private const val YACY_SEARCH_BASE = "https://yacy.searchlab.eu/yacysearch.html?query="
        private const val BING_SEARCH_BASE = "https://www.bing.com/search?q="
        // SearXNG bang modifiers explicitly select non-Bing web engines.
        // SearXNG's ! syntax is inclusive, so Bing is not selected here.
        private const val SEARXNG_ENGINE_PREFIX = "!ddg !br !qw !yh "
        // محركات الفيديو مدمجة داخل خيار "بحث فيديو" ولا تظهر في واجهة اختيار البحث.
        // يتم تمريرها إلى SearXNG كـ bang modifiers ليجمع نتائجها في صفحة واحدة.
        private const val VIDEO_SEARCH_ENGINE_PREFIX = "!gov !biv !brvid !yt !ptb !dm !od !qwv !ddv !kgv "
    }

    private lateinit var webViewContainer: FrameLayout
    private lateinit var editUrl: EditText
    private lateinit var progressBar: ProgressBar
    private lateinit var btnTabs: Button

    private val tabs = mutableListOf<Tab>()
    private var currentTabIndex = 0

    private var hideMedia = false
    private var nightMode = false
    private var mobileUA: String = ""
    private val desktopUA =
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) " +
                "Chrome/124.0.0.0 Safari/537.36"

    private var pendingStorageAction: (() -> Unit)? = null
    private val STORAGE_PERM_CODE = 4102
    private val ANDROID_PERM_CODE = 4103
    private val FILE_CHOOSER_CODE = 4104

    private var filePathCallback: ValueCallback<Array<Uri>>? = null
    private var pendingBookmarkExportContent: String? = null
    private var lastConfirmedSafetyUrl: String? = null
    // المواقع التي وافق المستخدم على فتحها خلال جلسة المتصفح؛
    // يسمح ذلك بالتحويلات داخل نفس الموقع بعد الضغط على "متابعة" دون إعادة التحذير.
    private val confirmedSafetyHosts = mutableSetOf<String>()
    private val bgExecutor = Executors.newFixedThreadPool(2)
    private val mainHandler = Handler(Looper.getMainLooper())

    private val PREFS = "browser_settings"
    private fun settingsPrefs() = getSharedPreferences(PREFS, Context.MODE_PRIVATE)

    private fun selectedSearchProvider(): String {
        val saved = settingsPrefs().getString(SEARCH_PROVIDER_KEY, SEARCH_GOOGLE) ?: SEARCH_GOOGLE
        // البحث المخصص أُزيل نهائيًا؛ إذا كانت هناك إعدادات قديمة له، نعود إلى Google.
        return if (saved == "custom") SEARCH_GOOGLE else saved
    }

    private fun saveSearchProvider(provider: String) {
        settingsPrefs().edit().putString(SEARCH_PROVIDER_KEY, provider).apply()
    }

    private fun savedFontZoom(): Int =
        settingsPrefs().getInt("fontZoom", 100).coerceIn(50, 200)

    private fun saveFontZoom(value: Int) {
        settingsPrefs().edit().putInt("fontZoom", value.coerceIn(50, 200)).apply()
    }

    private fun cameraAllowed() = settingsPrefs().getBoolean("camera", false)
    private fun micAllowed() = settingsPrefs().getBoolean("mic", false)
    private fun locationAllowed() = settingsPrefs().getBoolean("location", false)

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_browser)

        webViewContainer = findViewById(R.id.webViewContainer)
        editUrl = findViewById(R.id.editUrl)
        progressBar = findViewById(R.id.progressBar)
        val btnBookmarkStar = findViewById<Button>(R.id.btnBookmarkStar)
        val btnForward = findViewById<Button>(R.id.btnForward)
        btnTabs = findViewById(R.id.btnTabs)
        val btnBrowserMenu = findViewById<Button>(R.id.btnBrowserMenu)

        CookieManager.getInstance().setAcceptCookie(true)
        DownloadsRepository.ensureLoaded(this)
        AdBlocker.cleanupRemovedLists(this)
        hideMedia = settingsPrefs().getBoolean("hideMedia", false)
        nightMode = settingsPrefs().getBoolean("nightMode", false)

        editUrl.setOnEditorActionListener { _, actionId, event ->
            if (actionId == EditorInfo.IME_ACTION_GO ||
                (event != null && event.keyCode == KeyEvent.KEYCODE_ENTER)
            ) {
                loadFromAddressBar()
                hideKeyboard()
                true
            } else false
        }

        btnBookmarkStar.setOnClickListener { addCurrentPageToBookmarks() }
        btnForward.setOnClickListener {
            val tab = currentTab()
            if (!tab.isHome && tab.webView.canGoForward()) {
                tab.webView.goForward()
            } else {
                Toast.makeText(this, "لا توجد صفحة للتقدّم إليها", Toast.LENGTH_SHORT).show()
            }
        }
        btnTabs.setOnClickListener { showTabsDialog() }
        btnBrowserMenu.setOnClickListener { showBrowserMenu() }

        if (savedInstanceState != null && savedInstanceState.getInt("tabCount", -1) >= 0) {
            restoreTabsFromInstanceState(savedInstanceState)
        } else {
            restoreTabsOrCreateHome()
        }
        handleOpenUrlIntent(intent)
    }

    /**
     * يحوّل حالة WebView إلى نص قابل للحفظ بشكل دائم في SharedPreferences.
     * saveState() يحفظ سجل الرجوع/التقدم داخل WebView، لذلك لا يكفي حفظ URL الحالي فقط.
     */
    private fun serializeWebViewState(webView: WebView): String? {
        return try {
            val state = Bundle()
            val history = webView.saveState(state) ?: return null
            if (history.size <= 0) return null

            val parcel = Parcel.obtain()
            try {
                state.writeToParcel(parcel, 0)
                Base64.encodeToString(parcel.marshall(), Base64.NO_WRAP)
            } finally {
                parcel.recycle()
            }
        } catch (e: Exception) {
            null
        }
    }

    /** يعيد حالة WebView المحفوظة، بما فيها سجل الرجوع/التقدم. */
    private fun restoreSerializedWebViewState(webView: WebView, encoded: String?): Boolean {
        if (encoded.isNullOrBlank()) return false
        return try {
            val bytes = Base64.decode(encoded, Base64.DEFAULT)
            val parcel = Parcel.obtain()
            try {
                parcel.unmarshall(bytes, 0, bytes.size)
                parcel.setDataPosition(0)
                val state = Bundle.CREATOR.createFromParcel(parcel)
                state.classLoader = WebView::class.java.classLoader
                webView.restoreState(state) != null
            } finally {
                parcel.recycle()
            }
        } catch (e: Exception) {
            false
        }
    }

    override fun onSaveInstanceState(outState: Bundle) {
        super.onSaveInstanceState(outState)
        outState.putInt("tabCount", tabs.size)
        outState.putInt("currentTabIndex", currentTabIndex)
        tabs.forEachIndexed { i, tab ->
            outState.putBoolean("tab_${i}_isHome", tab.isHome)
            outState.putBoolean("tab_${i}_desktop", tab.desktopMode)
            outState.putStringArrayList("tab_${i}_back", ArrayList(tab.backStack))
            outState.putStringArrayList("tab_${i}_forward", ArrayList(tab.forwardStack))
            if (!tab.isHome) {
                val webState = Bundle()
                tab.webView.saveState(webState)
                outState.putBundle("tab_${i}_webstate", webState)
            }
        }
        // مهم: onSaveInstanceState وحده لا يكفي لإعادة تشغيل التطبيق لاحقًا.
        persistTabs()
    }

    /** يستعيد التبويبات من حالة أندرويد المحفوظة (تستخدم ذاكرة WebView المؤقتة بدل تحميل الصفحة من الإنترنت من جديد) */
    private fun restoreTabsFromInstanceState(state: Bundle) {
        val count = state.getInt("tabCount", 0)
        for (i in 0 until count) {
            val isHome = state.getBoolean("tab_${i}_isHome", true)
            val desktop = state.getBoolean("tab_${i}_desktop", false)
            val back = state.getStringArrayList("tab_${i}_back") ?: arrayListOf()
            val forward = state.getStringArrayList("tab_${i}_forward") ?: arrayListOf()
            val webState = state.getBundle("tab_${i}_webstate")

            val webView = WebView(this)
            setupWebView(webView)
            val cleanedUA = buildChromeLikeUserAgent(webView.settings.userAgentString)
            webView.settings.userAgentString = if (desktop) desktopUA else cleanedUA
            if (mobileUA.isEmpty()) mobileUA = cleanedUA

            val tab = Tab(id = System.currentTimeMillis() + i, webView = webView, isHome = isHome, desktopMode = desktop)
            tab.backStack.addAll(back)
            tab.forwardStack.addAll(forward)
            tabs.add(tab)

            if (!isHome && webState != null) {
                webView.restoreState(webState)
            }
        }
        val idx = state.getInt("currentTabIndex", 0).coerceIn(0, (tabs.size - 1).coerceAtLeast(0))
        if (tabs.isEmpty()) {
            createHomeTab()
        } else {
            switchToTab(idx)
        }
    }

    override fun onNewIntent(intent: Intent) {
        super.onNewIntent(intent)
        setIntent(intent)
        handleOpenUrlIntent(intent)
    }

    private fun handleOpenUrlIntent(intent: Intent?) {
        if (intent == null) return

        // الروابط القادمة من التطبيقات الأخرى (ومنها ChatGPT) تصل عادةً كـ ACTION_VIEW
        // مع URI في data. نفتحها دائمًا في تبويب جديد بدل استبدال التبويب الحالي.
        val extraUrl = intent.getStringExtra(EXTRA_OPEN_URL)
        val dataUrl = intent.data?.toString()
        val sharedText = intent.getStringExtra(Intent.EXTRA_TEXT)

        val url = listOf(extraUrl, dataUrl, sharedText)
            .asSequence()
            .mapNotNull { it?.trim()?.takeIf { value -> value.isNotBlank() } }
            .mapNotNull { value ->
                when {
                    value.startsWith("http://") || value.startsWith("https://") -> value
                    else -> null
                }
            }
            .firstOrNull()

        if (!url.isNullOrBlank()) {
            // كل رابط خارجي يفتح تبويبًا جديدًا، سواء وصل من ChatGPT أو WhatsApp أو Telegram
            // أو أي تطبيق آخر يدعم روابط الويب.
            createBrowsingTab(url)
        }
    }

    // ---------------- استعادة/حفظ التبويبات ----------------

    private fun restoreTabsOrCreateHome() {
        val (saved, currentIndex) = TabPersistence.load(this)
        if (saved.isEmpty()) {
            createHomeTab()
            return
        }
        saved.forEach { savedTab ->
            if (savedTab.isHome) {
                createTabInternal(isHome = true, url = null)
            } else {
                createTabInternal(
                    isHome = false,
                    url = savedTab.url,
                    restoredBack = savedTab.backStack,
                    restoredForward = savedTab.forwardStack,
                    restoredWebState = savedTab.webState
                )
            }
        }
        val idx = currentIndex.coerceIn(0, tabs.size - 1)
        switchToTab(idx)
    }

    private fun persistTabs() {
        val saved = tabs.map { tab ->
            SavedTab(
                tab.isHome,
                if (tab.isHome) "" else (tab.webView.url ?: ""),
                tab.title,
                tab.backStack.toList(),
                tab.forwardStack.toList(),
                if (tab.isHome) null else serializeWebViewState(tab.webView)
            )
        }
        TabPersistence.save(this, saved, currentTabIndex)
    }

    override fun onPause() {
        super.onPause()
        persistTabs()
    }

    // ---------------- إدارة التبويبات ----------------

    private fun createHomeTab() {
        createTabInternal(isHome = true, url = null)
        switchToTab(tabs.size - 1)
        persistTabs()
    }

    private fun createBrowsingTab(url: String) {
        createTabInternal(isHome = false, url = url)
        switchToTab(tabs.size - 1)
        persistTabs()
    }

    private fun createTabInternal(
        isHome: Boolean,
        url: String?,
        restoredBack: List<String> = emptyList(),
        restoredForward: List<String> = emptyList(),
        restoredWebState: String? = null
    ) {
        val webView = WebView(this)
        setupWebView(webView)
        val cleanedUA = buildChromeLikeUserAgent(webView.settings.userAgentString)
        webView.settings.userAgentString = cleanedUA
        if (mobileUA.isEmpty()) mobileUA = cleanedUA

        val tab = Tab(id = System.currentTimeMillis(), webView = webView, isHome = isHome)
        tab.backStack.addAll(restoredBack)
        tab.forwardStack.addAll(restoredForward)
        if (!isHome && !url.isNullOrBlank()) {
            tab.title = try { Uri.parse(url).host ?: url } catch (e: Exception) { url }
        }
        tabs.add(tab)

        if (!isHome) {
            // لا نعيد تحميل URL إذا كان لدينا WebView state محفوظ؛
            // restoreState يعيد سجل الرجوع/التقدم نفسه.
            val restored = restoreSerializedWebViewState(webView, restoredWebState)
            if (!restored && !url.isNullOrBlank()) {
                webView.loadUrl(url)
            }
        }
    }

    /** الرجوع والتقدم يعتمدان على سجل WebView الحقيقي مع استعادة موضع التمرير. */
    private fun goBackInTab(tab: Tab) {
        navigateHistory(tab, -1)
    }

    private fun goForwardInTab(tab: Tab) {
        navigateHistory(tab, 1)
    }

    // ---------------- حفظ واستعادة موضع التمرير (Scroll Position Restoration) ----------------

    private val blobBridge by lazy { BlobDownloadBridge(this) }

    private val SCROLL_RESTORE_INTERVAL_MS = 150L
    private val SCROLL_RESTORE_MAX_TRIES = 60          // ≈ 9 ثوانٍ كحد أقصى
    private val MAX_SAVED_SCROLL_ENTRIES = 100

    private fun rememberScroll(tab: Tab, url: String, y: Int) {
        if (url.isBlank() || url.startsWith("about:")) return
        tab.scrollPositions.remove(url)          // ليصبح الأحدث في آخر القائمة
        tab.scrollPositions[url] = y
        while (tab.scrollPositions.size > MAX_SAVED_SCROLL_ENTRIES) {
            val oldest = tab.scrollPositions.keys.firstOrNull() ?: break
            tab.scrollPositions.remove(oldest)
        }
    }

    /**
     * ينتقل في سجل التبويب خطوة للخلف (steps = -1) أو للأمام (steps = 1)،
     * ويعيد المستخدم إلى نفس مكان التمرير الذي كان فيه في تلك الصفحة.
     * يرجع false إذا لا توجد صفحة سابقة/تالية.
     */
    private fun navigateHistory(tab: Tab, steps: Int): Boolean {
        val wv = tab.webView
        val list = wv.copyBackForwardList()
        val targetIndex = list.currentIndex + steps
        if (targetIndex < 0 || targetIndex >= list.size) return false
        val targetUrl = list.getItemAtIndex(targetIndex)?.url

        // احفظ موضع الصفحة التي نغادرها (احتياطًا، المستمع يحفظه أصلًا أثناء التمرير)
        val leavingUrl = wv.url
        if (leavingUrl != null && !tab.pageLoading && tab.pendingRestoreY < 0) {
            rememberScroll(tab, leavingUrl, wv.scrollY)
        }

        cancelScrollRestore(tab)
        val savedY = targetUrl?.let { tab.scrollPositions[it] } ?: 0

        // عند الرجوع نفضّل النسخة المخزّنة مؤقتًا لتظهر نفس نتائج البحث التي رآها المستخدم
        wv.settings.cacheMode = WebSettings.LOAD_CACHE_ELSE_NETWORK
        wv.goBackOrForward(steps)

        if (savedY > 0) startScrollRestore(tab, targetIndex, savedY)
        return true
    }

    private fun cancelScrollRestore(tab: Tab) {
        tab.restoreGeneration++
        tab.pendingRestoreY = -1
    }

    private fun finishScrollRestore(tab: Tab) {
        tab.pendingRestoreY = -1
        try { tab.webView.settings.cacheMode = WebSettings.LOAD_DEFAULT } catch (e: Exception) { }
    }

    /**
     * يحاول كل 150ms تمرير الصفحة إلى الموضع المحفوظ حتى ينجح.
     * إذا كانت الصفحة أقصر من الموضع المطلوب (المحتوى لم يكتمل أو يُحمَّل بالتمرير اللانهائي مثل جوجل)،
     * يبقى التمرير عند آخر الصفحة المتاحة فيُحمَّل المزيد من المحتوى، ثم يكمل المحاولة.
     * تتوقف المحاولات إذا لمس المستخدم الشاشة.
     */
    private fun startScrollRestore(tab: Tab, targetIndex: Int, targetY: Int) {
        val generation = ++tab.restoreGeneration
        tab.pendingRestoreY = targetY
        var tries = 0
        val step = object : Runnable {
            override fun run() {
                if (tab.restoreGeneration != generation) return       // أُلغيت أو استُبدلت باستعادة أحدث
                if (!tabs.contains(tab)) return                        // التبويب أُغلق
                val wv = tab.webView
                tries++
                // لا نحرّك الصفحة القديمة: ننتظر حتى يصبح موضع السجل هو الصفحة الهدف
                val onTarget = try { wv.copyBackForwardList().currentIndex == targetIndex } catch (e: Exception) { false }
                if (onTarget) {
                    wv.scrollTo(wv.scrollX, targetY)
                    if (abs(wv.scrollY - targetY) <= 2 && !tab.pageLoading) {
                        finishScrollRestore(tab)
                        return
                    }
                }
                if (tries >= SCROLL_RESTORE_MAX_TRIES) {
                    finishScrollRestore(tab)
                    return
                }
                mainHandler.postDelayed(this, SCROLL_RESTORE_INTERVAL_MS)
            }
        }
        mainHandler.postDelayed(step, SCROLL_RESTORE_INTERVAL_MS)
    }

    private fun switchToTab(index: Int) {
        if (index < 0 || index >= tabs.size) return
        webViewContainer.removeAllViews()
        currentTabIndex = index
        val tab = tabs[index]

        if (tab.isHome) {
            editUrl.setText("")
            progressBar.visibility = View.GONE
            webViewContainer.addView(buildSpeedDialView())
        } else {
            (tab.webView.parent as? ViewGroup)?.removeView(tab.webView)
            webViewContainer.addView(
                tab.webView,
                ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT)
            )
            editUrl.setText(tab.webView.url ?: "")
        }
        updateTabCountUI()
    }

    private fun closeTab(index: Int) {
        if (index < 0 || index >= tabs.size) return
        val tab = tabs[index]
        (tab.webView.parent as? ViewGroup)?.removeView(tab.webView)
        tab.webView.destroy()
        tabs.removeAt(index)

        if (tabs.isEmpty()) {
            createHomeTab()
        } else {
            val newIndex = if (currentTabIndex >= tabs.size) tabs.size - 1 else currentTabIndex
            switchToTab(newIndex)
        }
        persistTabs()
    }

    private fun closeAllTabs() {
        webViewContainer.removeAllViews()
        tabs.forEach { it.webView.destroy() }
        tabs.clear()
        createHomeTab()
    }

    private fun updateTabCountUI() {
        btnTabs.text = tabs.size.toString()
    }

    private fun currentTab(): Tab = tabs[currentTabIndex]
    private fun currentWebView(): WebView = tabs[currentTabIndex].webView

    /** يزيل علامة "wv" (WebView) من هوية المتصفح الافتراضية لتقليل رفض بعض المواقع/إظهار تحقق زائد */
    private fun buildChromeLikeUserAgent(defaultUA: String): String {
        return defaultUA
            .replace("; wv)", ")")
            .replace(" wv;", "")
    }

    private fun hideKeyboard() {
        val imm = getSystemService(Context.INPUT_METHOD_SERVICE) as android.view.inputmethod.InputMethodManager
        imm.hideSoftInputFromWindow(editUrl.windowToken, 0)
        editUrl.clearFocus()
    }

    // ---------------- صفحة البداية (Speed Dial) ----------------

    private fun buildSpeedDialView(): View {
        val root = ScrollView(this).apply { setBackgroundColor(Color.BLACK) }

        val columns = 4
        val horizontalPadding = 16
        val screenWidth = resources.displayMetrics.widthPixels
        val cellWidth = (screenWidth - horizontalPadding * 2) / columns
        val iconSize = (cellWidth * 0.68f).toInt()

        val grid = GridLayout(this).apply {
            columnCount = columns
            alignmentMode = GridLayout.ALIGN_BOUNDS
            setPadding(horizontalPadding, 48, horizontalPadding, 48)
            layoutParams = ViewGroup.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
            )
        }

        val items = SpeedDialStorage.getItems(this)
        items.forEach { item ->
            grid.addView(buildSpeedDialTile(title = item.title, item = item, cellWidth = cellWidth, iconSize = iconSize) {
                createBrowsingTab(item.url)
            })
        }

        // زر + إضافة
        val addTile = buildAddTile(cellWidth = cellWidth, iconSize = iconSize) { showAddSpeedDialDialog() }
        grid.addView(addTile)

        root.addView(grid)
        return root
    }

    private fun buildAddTile(cellWidth: Int, iconSize: Int, onClick: () -> Unit): View {
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            gravity = Gravity.CENTER
            layoutParams = GridLayout.LayoutParams().apply {
                width = cellWidth
                setMargins(4, 12, 4, 12)
            }
            setOnClickListener { onClick() }
        }
        val plusBox = TextView(this).apply {
            text = "+"
            setTextColor(Color.WHITE)
            textSize = (iconSize / 22f).coerceAtLeast(20f)
            gravity = Gravity.CENTER
            layoutParams = LinearLayout.LayoutParams(iconSize, iconSize)
            setBackgroundColor(Color.parseColor("#222222"))
        }
        val label = TextView(this).apply {
            text = "إضافة"
            setTextColor(Color.LTGRAY)
            textSize = 12f
            gravity = Gravity.CENTER
            maxLines = 1
        }
        container.addView(plusBox)
        container.addView(label)
        return container
    }

    private fun buildSpeedDialTile(title: String, item: SpeedDialItem, cellWidth: Int, iconSize: Int, onClick: () -> Unit): View {
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            gravity = Gravity.CENTER
            layoutParams = GridLayout.LayoutParams().apply {
                width = cellWidth
                setMargins(4, 12, 4, 12)
            }
            setOnClickListener { onClick() }
            setOnLongClickListener {
                showSpeedDialItemMenu(item)
                true
            }
        }
        val icon = ImageView(this).apply {
            layoutParams = LinearLayout.LayoutParams(iconSize, iconSize).apply {
                gravity = Gravity.CENTER_HORIZONTAL
            }
            scaleType = ImageView.ScaleType.CENTER_INSIDE
            tag = item.url
        }
        loadFaviconInto(icon, item.url)

        val label = TextView(this).apply {
            text = title
            setTextColor(Color.parseColor("#808080"))
            textSize = 12f
            gravity = Gravity.CENTER
            maxLines = 1
            ellipsize = android.text.TextUtils.TruncateAt.END
        }
        container.addView(icon)
        container.addView(label)
        return container
    }

    private fun faviconCacheFile(host: String): File {
        val safe = Base64.encodeToString(
            host.toByteArray(Charsets.UTF_8),
            Base64.URL_SAFE or Base64.NO_WRAP
        )
        val dir = File(filesDir, "speeddial_favicons")
        if (!dir.exists()) dir.mkdirs()
        return File(dir, safe + ".png")
    }

    private fun loadFaviconInto(imageView: ImageView, pageUrl: String) {
        val host = try { Uri.parse(pageUrl).host?.lowercase(Locale.US) } catch (e: Exception) { null } ?: return
        val cacheFile = faviconCacheFile(host)

        // استخدم الصورة المحفوظة أولاً حتى لا تتحول مربعات المواقع إلى أسود عند كل تشغيل.
        bgExecutor.execute {
            var bitmap: Bitmap? = null
            if (cacheFile.exists()) {
                bitmap = runCatching { BitmapFactory.decodeFile(cacheFile.absolutePath) }.getOrNull()
            }

            if (bitmap == null) {
                var connection: HttpURLConnection? = null
                try {
                    val url = URL("https://www.google.com/s2/favicons?sz=128&domain=$host")
                    connection = url.openConnection() as HttpURLConnection
                    connection.connectTimeout = 8000
                    connection.readTimeout = 8000
                    bitmap = BitmapFactory.decodeStream(connection.inputStream)

                    bitmap?.let { downloaded ->
                        runCatching {
                            cacheFile.outputStream().use { out ->
                                downloaded.compress(Bitmap.CompressFormat.PNG, 100, out)
                            }
                        }
                    }
                } catch (e: Exception) {
                    bitmap = null
                } finally {
                    connection?.disconnect()
                }
            }

            val result = bitmap
            mainHandler.post {
                if (result != null && imageView.tag == pageUrl) {
                    imageView.setImageBitmap(result)
                }
            }
        }
    }
    private fun showAddSpeedDialDialog() {
        val input = EditText(this).apply {
            hint = "الصق الرابط هنا"
            setTextColor(Color.WHITE)
            setHintTextColor(Color.GRAY)
        }
        AlertDialog.Builder(this)
            .setTitle("إضافة موقع")
            .setView(input)
            .setPositiveButton("إضافة") { _, _ ->
                var url = input.text.toString().trim()
                if (url.isEmpty()) return@setPositiveButton
                if (!url.startsWith("http://") && !url.startsWith("https://")) url = "https://$url"
                val host = try { Uri.parse(url).host ?: url } catch (e: Exception) { url }
                SpeedDialStorage.addItem(this, host, url)
                switchToTab(currentTabIndex)
            }
            .setNegativeButton("إلغاء", null)
            .show()
    }

    private fun showSpeedDialItemMenu(item: SpeedDialItem) {
        AlertDialog.Builder(this)
            .setTitle(item.title)
            .setItems(arrayOf("إعادة تسمية", "حذف")) { _, which ->
                when (which) {
                    0 -> showRenameDialog(item)
                    1 -> {
                        SpeedDialStorage.removeItem(this, item.id)
                        switchToTab(currentTabIndex)
                    }
                }
            }
            .show()
    }

    private fun showRenameDialog(item: SpeedDialItem) {
        val input = EditText(this).apply {
            setText(item.title)
            setTextColor(Color.WHITE)
        }
        AlertDialog.Builder(this)
            .setTitle("إعادة تسمية")
            .setView(input)
            .setPositiveButton("حفظ") { _, _ ->
                SpeedDialStorage.renameItem(this, item.id, input.text.toString().trim())
                switchToTab(currentTabIndex)
            }
            .setNegativeButton("إلغاء", null)
            .show()
    }

    // ---------------- إعداد WebView ----------------

    private fun setupWebView(webView: WebView) {
        if (nightMode) webView.setBackgroundColor(Color.BLACK)
        webView.setLayerType(View.LAYER_TYPE_HARDWARE, null)
        val settings = webView.settings
        settings.textZoom = savedFontZoom()
        settings.javaScriptEnabled = true
        settings.domStorageEnabled = true
        settings.loadWithOverviewMode = true
        settings.useWideViewPort = true
        settings.loadsImagesAutomatically = true
        settings.blockNetworkImage = false
        settings.builtInZoomControls = true
        settings.displayZoomControls = false
        settings.mixedContentMode = WebSettings.MIXED_CONTENT_NEVER_ALLOW
        // النوافذ الجديدة تصل إلى onCreateWindow (مع نافذة التأكيد) فقط عند ضغط المستخدم؛
        // ما تفتحه الصفحة من نفسها بدون ضغط يبقى محجوبًا.
        settings.setSupportMultipleWindows(true)
        settings.javaScriptCanOpenWindowsAutomatically = false
        settings.allowFileAccess = true
        settings.blockNetworkImage = hideMedia
        settings.loadsImagesAutomatically = !hideMedia

        CookieManager.getInstance().setAcceptThirdPartyCookies(webView, true)

        // تسجيل موضع التمرير أثناء التصفح لكل رابط (يُستخدم عند الرجوع)
        webView.setOnScrollChangeListener { v, _, scrollY, _, _ ->
            val wv = v as? WebView ?: return@setOnScrollChangeListener
            val tab = tabs.find { it.webView == wv } ?: return@setOnScrollChangeListener
            if (tab.pageLoading || tab.pendingRestoreY >= 0) return@setOnScrollChangeListener
            val url = wv.url ?: return@setOnScrollChangeListener
            rememberScroll(tab, url, scrollY)
        }

        // إذا لمس المستخدم الشاشة أثناء الاستعادة نوقفها حتى لا نتحكم بتمريره
        webView.setOnTouchListener { v, event ->
            if (event.actionMasked == MotionEvent.ACTION_DOWN) {
                tabs.find { it.webView == v }?.let { t ->
                    if (t.pendingRestoreY >= 0) {
                        cancelScrollRestore(t)
                        try { t.webView.settings.cacheMode = WebSettings.LOAD_DEFAULT } catch (e: Exception) { }
                    }
                }
            }
            false
        }

        webView.webViewClient = object : WebViewClient() {
            override fun shouldInterceptRequest(
                view: WebView,
                request: WebResourceRequest
            ): WebResourceResponse? {
                AdBlocker.maybeBlock(this@BrowserActivity, request)?.let { return it }
                return super.shouldInterceptRequest(view, request)
            }

            override fun shouldOverrideUrlLoading(view: WebView, request: WebResourceRequest): Boolean {
                val url = request.url.toString()
                if (request.isForMainFrame && looksLikeDirectFileUrl(url)) {
                    DownloadsRepository.startNewDownload(
                        this@BrowserActivity,
                        url,
                        showToast = true,
                        userAgent = view.settings.userAgentString,
                        referer = view.url
                    )
                    return true
                }
                if (request.isForMainFrame) {
                    val known = DownloadsRepository.downloadList.find { it.url == url }
                    if (known != null) {
                        // رابط تنزيل معروف: كان يُتجاهل بصمت، الآن تظهر رسالة «الملف موجود: الاسم» أو يُستأنف التنزيل
                        DownloadsRepository.startNewDownload(
                            this@BrowserActivity, url, showToast = true, suggestedFileName = known.fileName,
                            userAgent = view.settings.userAgentString, referer = view.url
                        )
                        return true
                    }
                }
                if (request.isForMainFrame) {
                    navigateWithSafetyCheck(view, url)
                    return true
                }
                return false
            }

            override fun onPageStarted(view: WebView, url: String?, favicon: android.graphics.Bitmap?) {
                super.onPageStarted(view, url, favicon)
                tabs.find { it.webView == view }?.pageLoading = true
                // نحفظ الحالة فور بدء التنقل أيضًا حتى لا نفقد آخر خطوة إذا أُغلق التطبيق
                // قبل onPageFinished.
                persistTabs()
                if (nightMode) applyNightModeJs(view)
                if (isActiveTab(view)) editUrl.setText(url)
            }

            // أول ظهور لمحتوى الصفحة الجديدة: أسرع وقت لتطبيق الوضع الليلي
            override fun onPageCommitVisible(view: WebView, url: String?) {
                super.onPageCommitVisible(view, url)
                if (nightMode) applyNightModeJs(view)
            }

            override fun onPageFinished(view: WebView, url: String?) {
                super.onPageFinished(view, url)
                tabs.find { it.webView == view }?.let { t ->
                    t.pageLoading = false
                    // صفحة جديدة عادية (بدون استعادة جارية): سجّل موضعها الحالي
                    if (t.pendingRestoreY < 0) {
                        view.url?.let { u -> rememberScroll(t, u, view.scrollY) }
                        view.settings.cacheMode = WebSettings.LOAD_DEFAULT
                    }
                }
                if (url != null) {
                    recordVisitedNavigation(url)
                    BrowserStorage.addHistory(this@BrowserActivity, view.title ?: url, url)
                    applyVisitedSearchResultColors(view)
                }
                val resolvedTitle = view.title?.takeIf { it.isNotBlank() }
                    ?: url?.takeIf { it.isNotBlank() }
                    ?: "صفحة جديدة"
                tabs.find { it.webView == view }?.title = resolvedTitle
                if (nightMode) {
                    applyNightModeJs(view)
                    mainHandler.postDelayed({ if (nightMode) applyNightModeJs(view) }, 500)
                    // نحفظ حكم الصفحة (داكنة/فاتحة) لتُعالج أسرع في الزيارات القادمة
                    mainHandler.postDelayed({ if (nightMode) recordNightResult(view) }, 2200)
                }
                val tabForView = tabs.find { it.webView == view }
                if (tabForView?.desktopMode == true) applyDesktopViewportJs(view)
                if (isActiveTab(view)) {
                    if (hideMedia) applyHideMediaJs(view)
                }

                if (isSearchResultsPage(url)) {
                    // الحالة مبنية على سجل دائم، لذلك تبقى الألوان بعد الرجوع وإعادة فتح التطبيق.
                    applyVisitedSearchResultColors(view)
                    filterSearxngMicrosoftResults(view)
                    mainHandler.postDelayed({
                        if (!isFinishing && !isDestroyed && isSearchResultsPage(view.url)) {
                            applyVisitedSearchResultColors(view)
                            filterSearxngMicrosoftResults(view)
                        }
                    }, 700L)
                }

                // Keep translating every new page opened inside this translated tab.
                if (tabForView?.translationEnabled == true) {
                    mainHandler.postDelayed({
                        translateTabPageIfNeeded(view, tabForView)
                    }, 500L)
                }

                persistTabs()
            }
        }

        webView.webChromeClient = object : WebChromeClient() {
            override fun onProgressChanged(view: WebView, newProgress: Int) {
                if (nightMode && newProgress in 15..95 && System.currentTimeMillis() - lastNightInject > 250) {
                    applyNightModeJs(view)
                }
                if (isActiveTab(view)) {
                    progressBar.progress = newProgress
                    progressBar.visibility = if (newProgress >= 100) View.GONE else View.VISIBLE
                }
            }

            override fun onCreateWindow(
                view: WebView, isDialog: Boolean, isUserGesture: Boolean, resultMsg: android.os.Message
            ): Boolean {
                val transport = resultMsg.obj as? WebView.WebViewTransport ?: return false

                // نرد على الصفحة فورًا بـ WebView مؤقت يلتقط رابط النافذة فقط.
                // الاحتفاظ برسالة النافذة حتى يضغط المستخدم «سماح» كان يوقف التطبيق
                // (المتصفح يُلغي النافذة المعلّقة إذا طلبت الصفحة نافذة أخرى أو طال الانتظار).
                val temp = WebView(this@BrowserActivity)
                var finished = false

                fun dispose() {
                    if (finished) return
                    finished = true
                    // لا نهدم الـ WebView داخل ردّه نفسه: ننفّذ ذلك بعد انتهاء الاستدعاء الحالي
                    mainHandler.post {
                        try { temp.stopLoading() } catch (e: Exception) { }
                        try { temp.destroy() } catch (e: Exception) { }
                    }
                }

                fun capture(rawUrl: String?) {
                    if (finished) return
                    val u = rawUrl?.trim().orEmpty()
                    val lower = u.lowercase()
                    if (u.isEmpty() || lower.startsWith("about:") || lower.startsWith("javascript:") ||
                        lower.startsWith("data:") || lower.startsWith("blob:")) return
                    dispose()
                    showPopupConfirmDialog(u)
                }

                temp.webViewClient = object : WebViewClient() {
                    // لا نحمّل شيئًا من الشبكة داخل الـ WebView المؤقت
                    override fun shouldInterceptRequest(v: WebView, request: WebResourceRequest): WebResourceResponse? =
                        WebResourceResponse("text/plain", "utf-8", java.io.ByteArrayInputStream(ByteArray(0)))

                    override fun shouldOverrideUrlLoading(v: WebView, request: WebResourceRequest): Boolean {
                        capture(request.url.toString())
                        return true
                    }

                    override fun onPageStarted(v: WebView, url: String?, favicon: android.graphics.Bitmap?) {
                        capture(url)
                    }
                }

                transport.webView = temp
                resultMsg.sendToTarget()

                // إن لم يصل أي رابط (نافذة فارغة) نتخلص من الـ WebView المؤقت
                mainHandler.postDelayed({ dispose() }, 8000)
                return true
            }

            override fun onShowFileChooser(
                webView: WebView,
                callback: ValueCallback<Array<Uri>>,
                fileChooserParams: FileChooserParams
            ): Boolean {
                filePathCallback = callback
                val intent = Intent(Intent.ACTION_GET_CONTENT).apply {
                    addCategory(Intent.CATEGORY_OPENABLE)
                    type = "*/*"
                }
                try {
                    startActivityForResult(Intent.createChooser(intent, "اختر ملف"), FILE_CHOOSER_CODE)
                } catch (e: Exception) {
                    filePathCallback = null
                    return false
                }
                return true
            }

            override fun onPermissionRequest(request: PermissionRequest) {
                // نمنح فقط ما هو مسموح في إعدادات المتصفح، ونرفض الباقي
                val granted = request.resources.filter { res ->
                    when (res) {
                        PermissionRequest.RESOURCE_VIDEO_CAPTURE -> cameraAllowed()
                        PermissionRequest.RESOURCE_AUDIO_CAPTURE -> micAllowed()
                        PermissionRequest.RESOURCE_PROTECTED_MEDIA_ID -> true   // مطلوب لتشغيل فيديوهات DRM
                        else -> false
                    }
                }
                val deniedByUser = request.resources.any { res ->
                    (res == PermissionRequest.RESOURCE_VIDEO_CAPTURE && !cameraAllowed()) ||
                        (res == PermissionRequest.RESOURCE_AUDIO_CAPTURE && !micAllowed())
                }
                if (granted.isEmpty() || deniedByUser) {
                    request.deny()
                    return
                }

                val androidPerms = mutableListOf<String>()
                if (granted.contains(PermissionRequest.RESOURCE_VIDEO_CAPTURE)) androidPerms.add(Manifest.permission.CAMERA)
                if (granted.contains(PermissionRequest.RESOURCE_AUDIO_CAPTURE)) androidPerms.add(Manifest.permission.RECORD_AUDIO)

                runOnUiThread {
                    ensureAndroidPermissions(androidPerms.toTypedArray()) { ok ->
                        if (ok) request.grant(granted.toTypedArray()) else request.deny()
                    }
                }
            }

            override fun onGeolocationPermissionsShowPrompt(
                origin: String, callback: GeolocationPermissions.Callback
            ) {
                if (!locationAllowed()) {
                    callback.invoke(origin, false, false)
                    return
                }
                ensureAndroidPermissions(
                    arrayOf(Manifest.permission.ACCESS_FINE_LOCATION, Manifest.permission.ACCESS_COARSE_LOCATION),
                    anyOf = true
                ) { ok -> callback.invoke(origin, ok, false) }
            }
        }

        // جسر قراءة روابط blob: (محمي برمز عشوائي لكل عملية تنزيل)
        webView.addJavascriptInterface(blobBridge, "DownLS10Blob")

        webView.setDownloadListener { url, userAgent, contentDisposition, mimeType, _ ->
            val nameFromHeader = DownloadsRepository.fileNameFromContentDispositionOrNull(contentDisposition)
            if (url.startsWith("blob:", ignoreCase = true)) {
                blobBridge.start(webView, url, nameFromHeader, mimeType)
            } else {
                DownloadsRepository.startNewDownload(
                    this,
                    url,
                    showToast = true,
                    suggestedFileName = nameFromHeader,
                    userAgent = userAgent,
                    referer = webView.url,
                    mimeType = mimeType
                )
            }
        }
    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (requestCode == FILE_CHOOSER_CODE) {
            val results: Array<Uri>? = if (resultCode == Activity.RESULT_OK && data?.data != null) arrayOf(data.data!!) else null
            filePathCallback?.onReceiveValue(results)
            filePathCallback = null
            return
        }

        if (requestCode == BookmarksFileManager.EXPORT_REQUEST_CODE) {
            val content = pendingBookmarkExportContent
            pendingBookmarkExportContent = null
            if (resultCode == Activity.RESULT_OK && data?.data != null && content != null) {
                val result = BookmarksFileManager.writeExport(this, data.data!!, content)
                Toast.makeText(this, if (result.first) "تم تصدير العلامات المرجعية" else "فشل التصدير: ${result.second}", Toast.LENGTH_LONG).show()
            }
            return
        }

        if (requestCode == BookmarksFileManager.IMPORT_REQUEST_CODE) {
            if (resultCode == Activity.RESULT_OK && data?.data != null) {
                val result = BookmarksFileManager.readImport(this, data.data!!)
                val html = result.first
                if (html == null) {
                    Toast.makeText(this, "فشل الاستيراد: ${result.second}", Toast.LENGTH_LONG).show()
                } else {
                    val parsed = BrowserStorage.parseBookmarksHtml(html)
                    if (parsed.isEmpty()) {
                        Toast.makeText(this, "لم يتم العثور على علامات مرجعية في الملف", Toast.LENGTH_LONG).show()
                    } else {
                        val added = BrowserStorage.importBookmarks(this, parsed)
                        Toast.makeText(this, "تم استيراد $added علامة مرجعية جديدة", Toast.LENGTH_LONG).show()
                    }
                }
            }
        }
    }

    private fun isActiveTab(view: WebView): Boolean =
        tabs.isNotEmpty() && currentTabIndex < tabs.size && tabs[currentTabIndex].webView == view

    // ---------------- التنقل + فحص الأمان ----------------

    /** يسجّل الرابط كمزار. روابط جوجل الوسيطة (/url?q=...) تُفك ليُسجَّل الموقع الحقيقي. */
    private fun isVisitedSite(url: String?): Boolean {
        if (url.isNullOrBlank()) return false
        val host = try { Uri.parse(url).host } catch (e: Exception) { null }
        return VisitedSites.isVisited(this, host)
    }

    private fun visitedSiteColor(url: String?, unvisitedColor: Int = Color.CYAN): Int {
        return if (isVisitedSite(url)) Color.parseColor("#808080") else unvisitedColor
    }

    private fun isSearchResultsPage(url: String?): Boolean {
        if (url.isNullOrBlank()) return false
        val uri = try { Uri.parse(url) } catch (e: Exception) { return false }
        val host = uri.host?.lowercase(Locale.US) ?: return false
        val path = uri.path?.lowercase(Locale.US) ?: ""

        // محركات البحث المعروفة، بما فيها نطاقات Google المحلية مثل google.iq وgoogle.ae.
        val knownSearchHost =
            host == "google.com" || host.startsWith("google.") || host.endsWith(".google.com") ||
            host == "bing.com" || host.endsWith(".bing.com") ||
            host == "search.yahoo.com" ||
            host == "duckduckgo.com" || host.endsWith(".duckduckgo.com") ||
            host == "search.brave.com" ||
            host.endsWith(".yandex.com") || host.endsWith(".yandex.ru") ||
            host == "search.aol.com" ||
            host == "search.naver.com" ||
            host == "www.ecosia.org" ||
            host == "search.qwant.com"

        if (knownSearchHost) {
            return path.contains("search") ||
                uri.getQueryParameter("q") != null ||
                uri.getQueryParameter("query") != null ||
                uri.getQueryParameter("p") != null ||
                uri.getQueryParameter("text") != null
        }

        // دعم محركات البحث الأخرى التي تستخدم صفحة /search أو معاملات البحث الشائعة.
        return path == "/search" || path.startsWith("/search/") ||
            uri.getQueryParameter("q") != null ||
            uri.getQueryParameter("query") != null ||
            uri.getQueryParameter("search_query") != null
    }

    private fun filterSearxngMicrosoftResults(webView: WebView) {
        val host = try {
            Uri.parse(webView.url ?: "").host?.lowercase(Locale.US)
        } catch (_: Exception) {
            null
        }
        if (host != "searx.ononoki.org") return

        val js = """
            (function() {
                try {
                    var badHosts = ["bing.com", "microsoft.com"];

                    function isBadHost(host) {
                        host = String(host || "").toLowerCase().replace(/^www\./, "");
                        return badHosts.some(function(b) {
                            return host === b || host.endsWith("." + b);
                        });
                    }

                    document.querySelectorAll('a[href]').forEach(function(a) {
                        try {
                            var u = new URL(a.href, location.href);
                            if (!isBadHost(u.hostname)) return;

                            var card = a.closest("article.result, .result, li.result");
                            if (card) card.remove();
                        } catch (e) {}
                    });
                } catch (e) {}
            })();
        """
        webView.evaluateJavascript(js, null)
    }

    private fun applyVisitedSearchResultColors(webView: WebView) {
        val url = webView.url ?: return
        if (!isSearchResultsPage(url)) return

        val visitedUrlsJson = VisitedSites.allVisitedUrlsJson(this)
        val visitedHostsJson = VisitedSites.asJsonForInjection(this)
        val quotedUrlsJson = JSONObject.quote(visitedUrlsJson)
        val quotedHostsJson = JSONObject.quote(visitedHostsJson)

        val js = """
            (function(visitedUrlsRaw, visitedHostsRaw) {
                try {
                    var visitedUrls = JSON.parse(visitedUrlsRaw || '{}');
                    var visitedHosts = JSON.parse(visitedHostsRaw || '{}');
                    var PURPLE = '#800080';

                    function normalizeHost(host) {
                        return String(host || '')
                            .toLowerCase()
                            .replace(/^www\./, '')
                            .replace(/\.$/, '');
                    }

                    function normalize(u) {
                        try {
                            var x = new URL(u, location.href);
                            if (x.protocol !== 'http:' && x.protocol !== 'https:') return '';
                            x.hash = '';
                            var s = x.toString();
                            return s.endsWith('/') ? s.slice(0, -1) : s;
                        } catch (e) {
                            return '';
                        }
                    }

                    function unwrapGoogle(u) {
                        try {
                            var x = new URL(u, location.href);
                            var h = normalizeHost(x.hostname);
                            if ((h === 'google.com' || h.endsWith('.google.com') || h.indexOf('google.') === 0) &&
                                x.pathname === '/url') {
                                return x.searchParams.get('q') ||
                                       x.searchParams.get('url') ||
                                       x.searchParams.get('u') ||
                                       u;
                            }
                        } catch (e) {}
                        return u;
                    }

                    function isVisited(u) {
                        var unwrapped = unwrapGoogle(u);
                        var n = normalize(unwrapped);
                        if (!n) return false;

                        try {
                            var host = normalizeHost(new URL(unwrapped, location.href).hostname);
                            if (host) {
                                // تطابق النطاق نفسه، وكذلك النطاقات الفرعية للموقع.
                                if (visitedHosts[host]) return true;
                                var keys = Object.keys(visitedHosts);
                                for (var i = 0; i < keys.length; i++) {
                                    var visitedHost = normalizeHost(keys[i]);
                                    if (visitedHost &&
                                        (host === visitedHost ||
                                         host.endsWith('.' + visitedHost) ||
                                         visitedHost.endsWith('.' + host))) {
                                        return true;
                                    }
                                }
                            }
                        } catch (e) {}

                        if (visitedUrls[n]) return true;
                        var alt = n.endsWith('/') ? n.slice(0, -1) : n + '/';
                        return !!visitedUrls[alt];
                    }

                    function paintVisited(element) {
                        element.style.setProperty('color', PURPLE, 'important');
                        element.querySelectorAll('*').forEach(function(child) {
                            child.style.setProperty('color', PURPLE, 'important');
                        });
                    }

                    function styleResults() {
                        var links = document.querySelectorAll('a[href]');
                        for (var i = 0; i < links.length; i++) {
                            var a = links[i];
                            var href = a.href || a.getAttribute('href') || '';
                            if (!/^https?:/i.test(href)) continue;

                            var linkUrl;
                            try { linkUrl = new URL(href, location.href); } catch (e) { continue; }

                            var currentHost = normalizeHost(location.hostname);
                            var resultHost = normalizeHost(linkUrl.hostname);
                            if (resultHost === currentHost) continue;

                            if (!String(a.innerText || a.textContent || '').trim()) continue;

                            if (isVisited(href)) {
                                paintVisited(a);
                            }
                            // غير المزور: لا نضع أي لون من التطبيق، حتى يبقى
                            // اللون الأصلي الذي اختاره محرك البحث.
                        }
                    }

                    function scheduleStyle() {
                        if (window.__downls10VisitedColorTimer) {
                            clearTimeout(window.__downls10VisitedColorTimer);
                        }
                        window.__downls10VisitedColorTimer = setTimeout(function() {
                            window.__downls10VisitedColorTimer = null;
                            styleResults();
                        }, 80);
                    }

                    styleResults();

                    // محركات البحث الحديثة تغيّر class/style للنتائج بعد تحميلها.
                    // نراقب إضافة النتائج وتغييرات style/class حتى لا يعود الرابط المزور
                    // إلى اللون الأصلي بعد أن نلوّنه.
                    if (!window.__downls10VisitedColorObserver) {
                        window.__downls10VisitedColorObserver = new MutationObserver(function() {
                            scheduleStyle();
                        });

                        window.__downls10VisitedColorObserver.observe(document.documentElement, {
                            childList: true,
                            attributes: true,
                            attributeFilter: ['class', 'style'],
                            subtree: true
                        });

                        window.addEventListener('pageshow', styleResults);

                        // عدة محاولات قصيرة لأن بعض محركات البحث ترسم النتائج على مراحل.
                        [150, 400, 800, 1500, 3000].forEach(function(delay) {
                            setTimeout(styleResults, delay);
                        });
                    }
                } catch (e) {}
            })($quotedUrlsJson, $quotedHostsJson);
        """
        webView.evaluateJavascript(js, null)
    }

    private fun recordVisitedNavigation(url: String?) {
        if (url.isNullOrBlank()) return
        val uri = try { Uri.parse(url) } catch (e: Exception) { return }
        if (uri.scheme != "http" && uri.scheme != "https") return
        var realUrl = url
        val host = uri.host ?: return
        if (host.contains("google.") && uri.path == "/url") {
            val target = uri.getQueryParameter("q") ?: uri.getQueryParameter("url")
            if (!target.isNullOrBlank()) realUrl = target
        }
        val realHost = try { Uri.parse(realUrl).host } catch (e: Exception) { null }
        VisitedSites.recordVisit(this, realHost)
        VisitedSites.recordUrl(this, realUrl)
    }

    private fun loadAndRecord(webView: WebView, url: String) {
        recordVisitedNavigation(url)
        webView.loadUrl(url)
    }

    /** يلتقط روابط الملفات المباشرة حتى لو كان WebView يستطيع عرض نوع الملف داخله. */
    private fun looksLikeDirectFileUrl(rawUrl: String): Boolean {
        val uri = try { Uri.parse(rawUrl) } catch (_: Exception) { return false }
        val path = uri.path?.lowercase(Locale.US) ?: return false
        val ext = path.substringAfterLast('.', "")
        if (ext.isBlank() || ext.length > 10 || !ext.all { it.isLetterOrDigit() }) return false
        // صفحات الويب الديناميكية/العادية لا تُعامل كملفات.
        val webPageExtensions = setOf("html", "htm", "php", "asp", "aspx", "jsp", "cgi", "do", "action", "ashx", "axd", "pl")
        if (ext in webPageExtensions) return false
        // الامتدادات المعروفة للملفات التي يجب أن تنزل إلى Download.
        val fileExtensions = setOf(
            "apk", "aab", "zip", "rar", "7z", "tar", "gz", "bz2", "xz", "iso",
            "pdf", "epub", "mobi", "azw", "doc", "docx", "xls", "xlsx", "ppt", "pptx",
            "txt", "csv", "json", "xml", "rtf", "odt", "ods", "odp",
            "jpg", "jpeg", "png", "gif", "webp", "bmp", "svg", "ico", "tif", "tiff",
            "mp3", "wav", "ogg", "m4a", "flac", "aac",
            "mp4", "mkv", "avi", "mov", "webm", "3gp", "m4v",
            "srt", "ass", "vtt", "torrent", "bin", "dmg", "deb", "rpm", "msi", "exe",
            "jar", "war", "class", "db", "sqlite", "sql", "bak", "dat", "log"
        )
        return ext in fileExtensions
    }

    private fun isModApkWarningHost(host: String): Boolean {
        val h = host.lowercase(Locale.US).removePrefix("www.").removeSuffix(".")
        val explicitHosts = setOf(
            "modcda.com",
            "apkstime.com",
            "fastmodapk.com",
            "meigeeks.com",
            "pastebin.com",
            "greatmodapk.com",
            "downloadatoz.com"
        )
        if (explicitHosts.contains(h)) return true

        // تحذير استباقي للمواقع التي تحمل نمطاً واضحاً لمواقع MOD/APK.
        return h.contains("modapk") ||
            h.contains("apkmod") ||
            h.contains("mod-cda") ||
            h.contains("modcda") ||
            (h.contains("mod") && h.contains("apk"))
    }

    private fun navigateWithSafetyCheck(webView: WebView, rawUrl: String) {
        // روابط magnet وftp لا يفتحها المتصفح: تذهب لمدير التنزيل
        val lowerUrl = rawUrl.trim().lowercase()
        if (lowerUrl.startsWith("magnet:") || lowerUrl.startsWith("ftp://")) {
            DownloadsRepository.startNewDownload(this, rawUrl.trim(), showToast = true, referer = webView.url)
            return
        }
        // روابط ملفات Mega: صفحة Mega لا تستطيع التنزيل داخل WebView، فيتولاها مدير التنزيل مباشرة
        if (MegaSupport.isMegaFileLink(rawUrl.trim())) {
            DownloadsRepository.startNewDownload(this, rawUrl.trim(), showToast = true, referer = webView.url)
            return
        }
        // أي تنقل جديد (ضغط رابط/شريط العنوان) يستخدم الكاش الافتراضي وليس وضع الرجوع
        webView.settings.cacheMode = WebSettings.LOAD_DEFAULT
        tabs.find { it.webView == webView }?.let { cancelScrollRestore(it) }
        if (rawUrl == lastConfirmedSafetyUrl) {
            lastConfirmedSafetyUrl = null
            loadAndRecord(webView, rawUrl)
            return
        }

        val uri = try { Uri.parse(rawUrl) } catch (e: Exception) { null }

        // رابط مخصص (غير http/https): افتح التطبيق المثبّت إذا قدر يتعامل معه، وإلا تجاهله بهدوء
        if (uri?.scheme != null && uri.scheme != "http" && uri.scheme != "https") {
            openExternalAppLink(webView, rawUrl, uri)
            return
        }

        val host = uri?.host

        if (host != null) {
            val normalizedHost = host.lowercase(Locale.US).removePrefix("www.").removeSuffix(".")
            // بعد موافقة المستخدم، اسمح بالتنقلات والتحويلات داخل نفس الموقع خلال الجلسة.
            if (confirmedSafetyHosts.contains(normalizedHost)) {
                loadAndRecord(webView, rawUrl)
                return
            }

            val match = AdBlocker.matchSafetyCategory(this, host)
            val modApkWarning = isModApkWarningHost(normalizedHost)

            if (match != null || modApkWarning) {
                val warningParts = mutableListOf<String>()

                if (modApkWarning) {
                    warningParts.add(
                        "⚠️ هذا الموقع من المواقع التي طلبتَ إظهار تحذير لها؛ " +
                            "قد يحتوي على تطبيقات معدلة أو ملفات غير موثوقة. " +
                            "يمكنك المتابعة إذا كنت تريد فتحه."
                    )
                }

                if (match != null) {
                    when (match.category) {
                        ListCategory.PORN ->
                            warningParts.add("⚠️ هذا الموقع موجود في قائمة المحتوى الإباحي.")
                        ListCategory.MALWARE ->
                            warningParts.add("⚠️ هذا الموقع موجود في قائمة المواقع المصنفة ببرمجيات خبيثة.")
                        ListCategory.PHISHING ->
                            warningParts.add("⚠️ هذا الموقع موجود في قائمة مواقع التصيد الاحتيالي.")
                        ListCategory.RISK ->
                            warningParts.add("⚠️ هذا الموقع موجود في قائمة المواقع المشبوهة.")
                        ListCategory.AD -> Unit
                    }
                }

                AlertDialog.Builder(this)
                    .setTitle("تحذير قبل فتح الموقع")
                    .setMessage(
                        warningParts.joinToString("\n\n") +
                            "\n\nهل تريد فتح هذا الموقع؟"
                    )
                    .setPositiveButton("متابعة") { _, _ ->
                        lastConfirmedSafetyUrl = rawUrl
                        if (!normalizedHost.isBlank()) {
                            confirmedSafetyHosts.add(normalizedHost)
                        }
                        loadAndRecord(webView, rawUrl)
                    }
                    .setNegativeButton("رفض", null)
                    .show()
                return
            }
        }

        // السماح بفتح روابط HTTP بشكل طبيعي بدون رسالة تحذير تمنع/تربك المستخدم.
        // لا يتم تحويل HTTP إلى HTTPS هنا؛ يجب تحميل العنوان الذي أدخله المستخدم كما هو.
        loadAndRecord(webView, rawUrl)
    }

    // يفتح روابط التطبيقات الخارجية (Google Play, تيليجرام, واتساب, ...).
    // روابط "intent://" (مثل زر "الفتح في تطبيق Play") لها تنسيق خاص يجب فكّه
    // بواسطة Intent.parseUri وليس ببناء Intent يدويًا من الـ Uri مباشرة.
    private fun openExternalAppLink(webView: WebView, rawUrl: String, uri: Uri) {
        try {
            val intent: Intent
            var fallbackUrl: String? = null

            if (uri.scheme == "intent") {
                intent = Intent.parseUri(rawUrl, Intent.URI_INTENT_SCHEME)
                fallbackUrl = intent.getStringExtra("browser_fallback_url")
                // نتأكد إنه ما يرجع لنفس المتصفح إذا التطبيق موجود أصلاً
                intent.addCategory(Intent.CATEGORY_BROWSABLE)
                intent.component = null
                intent.selector = null
            } else {
                intent = Intent(Intent.ACTION_VIEW, uri)
            }

            if (intent.resolveActivity(packageManager) != null) {
                startActivity(intent)
            } else if (!fallbackUrl.isNullOrBlank()) {
                // التطبيق غير مثبّت: افتح الرابط الاحتياطي (عادة صفحة متجر التطبيق نفسه)
                loadAndRecord(webView, fallbackUrl)
            }
            // ما فيه تطبيق ولا رابط احتياطي: تجاهل بهدوء
        } catch (e: Exception) {
            // تجاهل بهدوء عند فشل تحليل أو فتح الرابط
        }
    }

    private fun showBlockedInterstitial(webView: WebView, message: String) {
        val html = """
            <html dir="rtl"><body style="background:#000;color:#fff;font-family:sans-serif;
            display:flex;align-items:center;justify-content:center;height:100vh;margin:0;">
            <h2>🚫 $message</h2></body></html>
        """
        webView.loadDataWithBaseURL(null, html, "text/html", "UTF-8", null)
    }

    private fun buildSearchUrl(query: String): String {
        val encoded = Uri.encode(query)
        return when (selectedSearchProvider()) {
            SEARCH_SEARXNG -> SEARXNG_SEARCH_BASE + Uri.encode(SEARXNG_ENGINE_PREFIX + query)
            SEARCH_VIDEO -> SEARXNG_SEARCH_BASE + Uri.encode(VIDEO_SEARCH_ENGINE_PREFIX + query)
            SEARCH_METAGER -> METAGER_SEARCH_BASE + encoded
            SEARCH_4GET -> FOURGET_SEARCH_BASE + encoded
            SEARCH_LIBREY -> LIBREY_SEARCH_BASE + encoded
            SEARCH_MOJEEK -> MOJEEK_SEARCH_BASE + encoded
            SEARCH_BRAVE -> BRAVE_SEARCH_BASE + encoded
            SEARCH_YACY -> YACY_SEARCH_BASE + encoded
            SEARCH_BING -> BING_SEARCH_BASE + encoded
            else -> "https://www.google.com/search?q=" + encoded
        }
    }

    private fun loadFromAddressBar() {
        var input = editUrl.text.toString().trim()
        if (input.isEmpty()) return

        input = when {
            Patterns.WEB_URL.matcher(input).matches() && !input.startsWith("http") -> "https://$input"
            input.contains(" ") || !input.contains(".") -> {
                val searchUrl = buildSearchUrl(input)
                searchUrl
            }
            !input.startsWith("http://") && !input.startsWith("https://") -> "https://$input"
            else -> input
        }

        if (currentTab().isHome) {
            currentTab().isHome = false
            webViewContainer.removeAllViews()
            webViewContainer.addView(
                currentWebView(),
                ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT)
            )
        }
        navigateWithSafetyCheck(currentWebView(), input)
    }

    // ---------------- قائمة ☰ ----------------

    private fun showBrowserMenu() {
        val options = arrayOf(
            "تنزيل",
            if (hideMedia) "إظهار الوسائط" else "إخفاء الوسائط بالكامل",
            "العلامات المرجعية",
            if (currentTab().desktopMode) "عرض الجوال" else "عرض سطح المكتب",
            "مانع الإعلانات وحماية التصفح",
            "تكبير/تصغير الخط",
            "السجل",
            "ترجمة إلى العربية",
            "الأذونات",
            "البحث",
            if (nightMode) "إيقاف الوضع الليلي" else "تفعيل الوضع الليلي"
        )

        AlertDialog.Builder(this)
            .setTitle("خيارات المتصفح")
            .setItems(options) { _, which ->
                when (which) {
                    0 -> openDownLS10()
                    1 -> toggleHideMedia()
                    2 -> showBookmarksDialog()
                    3 -> toggleDesktopMode()
                    4 -> showAdBlockSettingsDialog()
                    5 -> showFontZoomDialog()
                    6 -> showHistoryDialog()
                    7 -> runTranslate()
                    8 -> showPermissionsDialog()
                    9 -> showSearchProviderDialog()
                    10 -> toggleNightMode()
                }
            }
            .show()
    }

    private fun showSearchProviderDialog() {
        val providers = arrayOf(
            SEARCH_SEARXNG to "بحث SearXNG",
            SEARCH_GOOGLE to "Google",
            SEARCH_METAGER to "MetaGer",
            SEARCH_4GET to "4get",
            SEARCH_LIBREY to "LibreY",
            SEARCH_MOJEEK to "Mojeek",
            SEARCH_BRAVE to "Brave Search",
            SEARCH_YACY to "YaCy",
            SEARCH_BING to "Bing",
            SEARCH_VIDEO to "بحث فيديو"
        )
        val selected = selectedSearchProvider()
        val items = providers.map { (id, label) ->
            if (id == selected) "$label    ✅" else label
        }.toTypedArray()

        AlertDialog.Builder(this)
            .setTitle("البحث")
            .setItems(items) { dialog, which ->
                saveSearchProvider(providers[which].first)
                dialog.dismiss()
            }
            .setNegativeButton("إغلاق", null)
            .show()
    }

    // 6) السجل
    private fun showHistoryDialog() {
        val history = BrowserStorage.getHistory(this)
        if (history.isEmpty()) {
            Toast.makeText(this, "السجل فارغ", Toast.LENGTH_SHORT).show()
            return
        }

        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(24, 16, 24, 16)
        }
        val scroll = ScrollView(this).apply { addView(container) }

        history.forEach { entry ->
            val displayText = entry.title.ifBlank { entry.url }
            val row = TextView(this).apply {
                text = displayText
                setTextColor(Color.WHITE)
                textSize = 14f
                maxLines = 2
                ellipsize = android.text.TextUtils.TruncateAt.END
                setPadding(0, 20, 0, 20)
                setOnClickListener { createBrowsingTab(entry.url) }
            }
            container.addView(row)
            container.addView(View(this).apply {
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 1)
                setBackgroundColor(Color.parseColor("#333333"))
            })
        }

        AlertDialog.Builder(this)
            .setTitle("سجل التصفح")
            .setView(scroll)
            .setPositiveButton("مسح السجل") { _, _ -> BrowserStorage.clearHistory(this) }
            .setNegativeButton("إغلاق", null)
            .show()
    }

    // 7) ترجمة إلى العربية
    private fun runTranslate() {
        val tab = currentTab()
        if (tab.isHome) {
            Toast.makeText(this, "لا توجد صفحة لترجمتها", Toast.LENGTH_SHORT).show()
            return
        }

        // Translation remains enabled for this tab; every new page is translated automatically.
        tab.translationEnabled = true
        tab.lastTranslatedUrl = ""
        tab.translationInProgress = false
        Toast.makeText(this, "جاري ترجمة الموقع إلى العربية...", Toast.LENGTH_SHORT).show()
        translateTabPageIfNeeded(tab.webView, tab)
    }

    private fun translateTabPageIfNeeded(webView: WebView, tab: Tab) {
        if (!tab.translationEnabled || tab.translationInProgress) return
        val url = webView.url?.takeIf { it.startsWith("http://") || it.startsWith("https://") } ?: return
        if (url == tab.lastTranslatedUrl) return

        tab.translationInProgress = true
        PageTranslator.translatePage(webView, "ar") { success, message ->
            tab.translationInProgress = false
            if (success) tab.lastTranslatedUrl = url
            if (isActiveTab(webView) && !isFinishing) {
                Toast.makeText(this, message, Toast.LENGTH_SHORT).show()
            }
        }
    }

    // ---------------- قائمة التبويبات ----------------

    private fun showTabsDialog() {
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(24, 16, 24, 16)
        }
        val scroll = ScrollView(this).apply { addView(container) }

        val dialog = AlertDialog.Builder(this)
            .setTitle("الصفحات المفتوحة")
            .setView(scroll)
            .setNegativeButton("إغلاق", null)
            .create()

        fun refresh() {
            container.removeAllViews()
            tabs.forEachIndexed { index, tab ->
                val row = LinearLayout(this).apply {
                    orientation = LinearLayout.HORIZONTAL
                    gravity = Gravity.CENTER_VERTICAL
                    setPadding(0, 20, 0, 20)
                }
                val label = if (tab.isHome) "الصفحة الرئيسية" else tab.title
                val tabUrl = if (tab.isHome) null else tab.webView.url
                val titleText = TextView(this).apply {
                    text = if (index == currentTabIndex) "● $label" else label
                    setTextColor(Color.WHITE)
                    textSize = 15f
                    maxLines = 2
                    ellipsize = android.text.TextUtils.TruncateAt.END
                    layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
                    setOnClickListener {
                        switchToTab(index)
                        dialog.dismiss()
                    }
                }
                val closeBtn = Button(this).apply {
                    text = "✕"
                    setTextColor(Color.WHITE)
                    setPadding(24, 0, 24, 0)
                    setOnClickListener {
                        closeTab(index)
                        refresh()
                    }
                }
                row.addView(titleText)
                row.addView(closeBtn)
                container.addView(row)

                container.addView(View(this).apply {
                    layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 1)
                    setBackgroundColor(Color.parseColor("#333333"))
                })
            }

            val actionsRow = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                setPadding(0, 24, 0, 0)
            }
            val addBtn = Button(this).apply {
                text = "+ إضافة صفحة جديدة"
                layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
                setOnClickListener {
                    createHomeTab()
                    dialog.dismiss()
                }
            }
            val closeAllBtn = Button(this).apply {
                text = "إغلاق الكل"
                layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
                setOnClickListener {
                    closeAllTabs()
                    dialog.dismiss()
                }
            }
            actionsRow.addView(addBtn)
            actionsRow.addView(closeAllBtn)
            container.addView(actionsRow)
        }

        refresh()
        dialog.show()
    }

    override fun onBackPressed() {
        val tab = currentTab()
        if (!tab.isHome && navigateHistory(tab, -1)) {
            return
        }
        if (!tab.isHome) {
            tab.isHome = true
            switchToTab(currentTabIndex)
            persistTabs()
            return
        }
        finishAffinity()
    }

    override fun onDestroy() {
        tabs.forEach { it.webView.destroy() }
        super.onDestroy()
    }
}
