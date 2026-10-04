package cn.qwe.player

import android.Manifest
import android.annotation.SuppressLint
import android.app.Activity
import android.app.Application
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.ContentUris
import android.content.Context
import android.content.Intent
import android.content.pm.ServiceInfo
import android.content.res.Configuration
import android.media.AudioFormat
import android.media.AudioManager
import android.media.AudioRecord
import android.media.MediaRecorder
import android.media.audiofx.DynamicsProcessing
import android.media.audiofx.Equalizer
import android.media.audiofx.BassBoost
import android.media.audiofx.PresetReverb
import android.media.audiofx.Virtualizer
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Environment
import android.os.IBinder
import android.provider.MediaStore
import android.view.WindowManager
import androidx.activity.ComponentActivity
import androidx.activity.compose.rememberLauncherForActivityResult
import androidx.activity.compose.setContent
import androidx.activity.result.contract.ActivityResultContracts
import androidx.compose.animation.*
import androidx.compose.animation.core.*
import androidx.compose.foundation.*
import androidx.compose.foundation.gestures.awaitEachGesture
import androidx.compose.foundation.gestures.awaitFirstDown
import androidx.compose.foundation.gestures.detectDragGestures
import androidx.compose.foundation.gestures.detectTapGestures
import androidx.compose.foundation.gestures.snapping.rememberSnapFlingBehavior
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.interaction.collectIsPressedAsState
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.lazy.*
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.foundation.text.BasicTextField
import androidx.compose.foundation.text.KeyboardActions
import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.rounded.*
import androidx.compose.material3.*
import androidx.compose.material3.TabRowDefaults.tabIndicatorOffset
import androidx.compose.runtime.*
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.*
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.BlendMode
import androidx.compose.ui.graphics.Brush
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.CompositingStrategy
import androidx.compose.ui.graphics.Shadow
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.graphics.vector.ImageVector
import androidx.compose.ui.graphics.vector.rememberVectorPainter
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.layout.onGloballyPositioned
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalSoftwareKeyboardController
import androidx.compose.ui.text.TextStyle
import androidx.compose.ui.text.font.Font
import androidx.compose.ui.text.font.FontFamily
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.input.ImeAction
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.text.style.TextOverflow
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
import androidx.compose.ui.unit.max
import androidx.core.app.NotificationCompat
import androidx.lifecycle.AndroidViewModel
import androidx.lifecycle.viewModelScope
import androidx.lifecycle.viewmodel.compose.viewModel
import androidx.media3.common.AudioAttributes
import androidx.media3.common.C
import androidx.media3.common.MediaItem
import androidx.media3.common.PlaybackException
import androidx.media3.common.Player
import androidx.media3.exoplayer.ExoPlayer
import androidx.media3.session.MediaSession
import coil.compose.AsyncImage
import coil.request.ImageRequest
import cn.qwe.player.ui.theme.QwePlayerTheme
import com.k2fsa.sherpa.onnx.*
import kotlinx.coroutines.*
import org.jaudiotagger.audio.AudioFileIO
import org.jaudiotagger.tag.FieldKey
import java.io.File
import java.net.DatagramPacket
import java.net.DatagramSocket
import java.net.URLDecoder
import kotlin.math.abs
import kotlin.math.min
import kotlin.math.sqrt

// ==========================================
// 1. 数据模型与辅助算法 & 中文拼音/中英艺人映射引擎
// ==========================================
data class Song(
    val id: Long, val title: String, val artist: String,
    val uri: Uri, val albumArtUri: Uri, val dataPath: String, val duration: Long
)

data class CustomPlaylist(val name: String, val file: File, val songs: List<Song>)
data class LrcRow(val timeInMs: Long, val text: String)

enum class VoiceState { IDLE, RECORDING, RECOGNIZING, SUCCESS_TIP }
enum class PlayMode { SEQUENCE, SHUFFLE, REPEAT_ONE }

fun levenshteinDistance(s: String, t: String): Int {
    if (s == t) return 0
    if (s.isEmpty()) return t.length
    if (t.isEmpty()) return s.length
    val v0 = IntArray(t.length + 1) { it }
    val v1 = IntArray(t.length + 1)
    for (i in s.indices) {
        v1[0] = i + 1
        for (j in t.indices) {
            val cost = if (s[i] == t[j]) 0 else 1
            v1[j + 1] = minOf(v1[j] + 1, v0[j + 1] + 1, v0[j] + cost)
        }
        for (j in 0..t.length) v0[j] = v1[j]
    }
    return v1[t.length]
}

fun lerpFloat(start: Float, stop: Float, fraction: Float): Float = start + (stop - start) * fraction
fun lerpDp(start: Dp, stop: Dp, fraction: Float): Dp = Dp(start.value + (stop.value - start.value) * fraction)
val SnappyDecelerateEasing = CubicBezierEasing(0.12f, 0.85f, 0.18f, 1f)

fun getCustomFontFamily(context: Context, fontName: String): FontFamily {
    return try {
        val resId = context.resources.getIdentifier(fontName, "font", context.packageName)
        if (resId != 0) FontFamily(Font(resId)) else FontFamily.Default
    } catch (_: Exception) {
        FontFamily.Default
    }
}

fun getPinyinFirstLetter(c: Char): Char {
    val code = c.code
    if (code in 0x4E00..0x9FA5) {
        return when (code) {
            in 0x4E00..0x4ED7 -> 'A'
            in 0x4ED8..0x4FCF -> 'B'
            in 0x4FD0..0x5179 -> 'C'
            in 0x517A..0x536F -> 'D'
            in 0x5370..0x541F -> 'E'
            in 0x5420..0x573F -> 'F'
            in 0x5740..0x5913 -> 'G'
            in 0x5914..0x5ABF -> 'H'
            in 0x5AC0..0x5D1F -> 'J'
            in 0x5D20..0x5F13 -> 'K'
            in 0x5F14..0x624F -> 'L'
            in 0x6250..0x661F -> 'M'
            in 0x6620..0x681F -> 'N'
            in 0x6820..0x6B9F -> 'O'
            in 0x6BA0..0x6D4F -> 'P'
            in 0x6D50..0x705F -> 'Q'
            in 0x7060..0x743F -> 'R'
            in 0x7440..0x77EF -> 'S'
            in 0x77F0..0x7B9F -> 'T'
            in 0x7BA0..0x811F -> 'W'
            in 0x8120..0x857F -> 'X'
            in 0x8580..0x897F -> 'Y'
            in 0x8980..0x9FA5 -> 'Z'
            else -> '#'
        }
    }
    if (c in 'A'..'Z' || c in 'a'..'z') return c.uppercaseChar()
    return '#'
}

fun getInitialLetter(text: String): Char {
    if (text.isBlank()) return '#'
    return getPinyinFirstLetter(text.trim().first())
}

// ==========================================
// 中英文歌手别名/译名知识库
// ==========================================
object ArtistAliasEngine {
    private val aliasGroups = listOf(
        listOf("艾薇儿", "艾薇尔", "avril lavigne", "avril"),
        listOf("泰勒斯威夫特", "霉霉", "泰勒", "taylor swift", "taylor"),
        listOf("周杰伦", "jay chou", "jay"),
        listOf("林俊杰", "jj lin", "jj"),
        listOf("陈奕迅", "eason chan", "eason"),
        listOf("邓紫棋", "g.e.m.", "gem", "g.e.m"),
        listOf("张学友", "jacky cheung"),
        listOf("刘德华", "andy lau"),
        listOf("王力宏", "wang leehom", "leehom"),
        listOf("陶喆", "david tao"),
        listOf("李荣浩", "younghope"),
        listOf("薛之谦", "joker xue"),
        listOf("华晨宇", "huachenyu"),
        listOf("毛不易", "maobuyi"),
        listOf("汪苏泷", "silence wang"),
        listOf("许嵩", "vae"),
        listOf("朴树", "pu shu"),
        listOf("李健", "li jian"),
        listOf("孙燕姿", "stefanie sun", "yanzi sun"),
        listOf("梁静茹", "fish leong"),
        listOf("蔡依林", "jolin tsai", "jolin"),
        listOf("张韶涵", "angela chang"),
        listOf("王菲", "faye wong"),
        listOf("莫文蔚", "karen mok"),
        listOf("田馥甄", "hebe", "hebe tien"),
        listOf("张惠妹", "a-mei", "amei"),
        listOf("五月天", "mayday"),
        listOf("苏打绿", "sodagreen"),
        listOf("告五人", "accusefive"),
        listOf("新裤子", "new pants"),
        listOf("痛仰乐队", "痛仰", "tong yang"),
        listOf("二手玫瑰", "second hand rose"),
        listOf("草东没有派对", "草东", "no party for cao dong"),
        listOf("落日飞车", "sunset rollercoaster"),
        listOf("迈克尔杰克逊", "迈克尔·杰克逊", "杰克逊", "michael jackson", "mj"),
        listOf("贾斯汀比伯", "比伯", "justin bieber", "bieber"),
        listOf("布兰妮", "小甜甜", "britney spears", "britney"),
        listOf("阿黛尔", "adele", "adele adkins"),
        listOf("蕾哈娜", "日日", "rihanna", "riri"),
        listOf("席琳迪翁", "celine dion"),
        listOf("玛丽亚凯莉", "牛姐", "mariah carey"),
        listOf("西城男孩", "westlife"),
        listOf("后街男孩", "backstreet boys", "bsb"),
        listOf("林肯公园", "linkin park", "lp"),
        listOf("梦龙", "梦龙乐队", "谜幻乐团", "imagine dragons"),
        listOf("火星哥", "布鲁诺马斯", "bruno mars"),
        listOf("戳爷", "特洛伊希文", "troye sivan"),
        listOf("断眉", "查理普斯", "charlie puth"),
        listOf("黄老板", "艾德希兰", "ed sheeran"),
        listOf("碧昂丝", "碧昂斯", "beyonce", "beyoncé"),
        listOf("爱莉安娜格兰德", "爱莉安娜", "a妹", "ariana grande"),
        listOf("卡妹", "卡米拉", "camila cabello"),
        listOf("啪姐", "杜阿利帕", "dua lipa"),
        listOf("盆栽哥", "威肯", "the weeknd", "weeknd"),
        listOf("酷玩乐队", "酷玩", "coldplay"),
        listOf("魔力红", "maroon 5", "maroon5"),
        listOf("烟鬼", "烟鬼组合", "the chainsmokers"),
        listOf("皇后乐队", "皇后", "queen"),
        listOf("甲壳虫", "披头士", "the beatles", "beatles"),
        listOf("猫王", "elvis presley"),
        listOf("艾伦沃克", "alan walker"),
        listOf("棉花糖", "marshmello"),
        listOf("电音教父", "avicii", "a神"),
        listOf("卡尔文哈里斯", "calvin harris"),
        listOf("姆爷", "埃米纳姆", "eminem"),
        listOf("侃爷", "肯伊威斯特", "kanye west", "ye"),
        listOf("德雷克", "公鸭", "drake"),
        listOf("拉娜德雷", "打雷姐", "lana del rey"),
        listOf("比莉艾利什", "碧梨", "billie eilish"),
        listOf("奥利维亚罗德里戈", "啪妹", "olivia rodrigo"),
        listOf("花泽香菜", "hanazawa kana"),
        listOf("米津玄师", "八爷", "kenshi yonezu", "yonezu kenshi"),
        listOf("织部里沙", "lisa", "lisa oliver"),
        listOf("中岛美嘉", "nakashima mika"),
        listOf("宇多田光", "utada hikaru"),
        listOf("滨崎步", "ayumi hamasaki"),
        listOf("久石让", "joe hisaishi"),
        listOf("坂本龙一", "ryuichi sakamoto"),
        listOf("泽野弘之", "hiroyuki sawano"),
        listOf("防弹少年团", "bts"),
        listOf("黑粉", "粉墨", "blackpink"),
        listOf("少女时代", "girls' generation", "snsd"),
        listOf("权志龙", "g-dragon", "gd"),
        listOf("李知恩", "iu"),
        listOf("金泰妍", "泰妍", "taeyeon"),
        listOf("边伯贤", "伯贤", "baekhyun"),
        listOf("林允儿", "允儿", "yoona"),
        listOf("朴彩英", "rose", "rosé"),
        listOf("金智秀", "jisoo"),
        listOf("金智妮", "jennie"),
        listOf("王嘉尔", "jackson wang"),
        listOf("张艺兴", "lay"),
        listOf("鹿晗", "luhan")
    )

    fun getAliases(name: String): Set<String> {
        val cleanName = name.trim().lowercase()
        val result = mutableSetOf(cleanName)
        for (group in aliasGroups) {
            if (group.any { cleanName == it || cleanName.contains(it) || it.contains(cleanName) }) {
                result.addAll(group)
            }
        }
        return result
    }

    fun isArtistMatch(query: String, artistName: String): Boolean {
        val q = query.trim().lowercase()
        val a = artistName.trim().lowercase()
        if (q.isEmpty() || a.isEmpty()) return false
        if (a == q || a.contains(q) || q.contains(a)) return true

        val queryAliases = getAliases(q)
        val artistAliases = getAliases(a)

        if (queryAliases.intersect(artistAliases).isNotEmpty()) return true

        for (qAlias in queryAliases) {
            for (aAlias in artistAliases) {
                if (aAlias.contains(qAlias) || qAlias.contains(aAlias)) return true
                if (levenshteinDistance(qAlias, aAlias) <= maxOf(1, minOf(qAlias.length, aAlias.length) / 3)) return true
            }
        }
        return false
    }
}

fun Modifier.voicePressHandler(
    onPressStart: () -> Unit,
    onPressEnd: () -> Unit
): Modifier = this.pointerInput(Unit) {
    var lastTriggerTime = 0L
    val debounceMs = 400L

    awaitEachGesture {
        val down = awaitFirstDown(requireUnconsumed = false)
        down.consume()

        val now = System.currentTimeMillis()
        val isValidPress = (now - lastTriggerTime) > debounceMs

        if (isValidPress) {
            onPressStart()
            lastTriggerTime = now
        }

        var isDown = true
        while (isDown) {
            val event = awaitPointerEvent()
            val anyPressed = event.changes.any { it.pressed }
            if (!anyPressed) {
                isDown = false
                if (isValidPress) {
                    onPressEnd()
                    lastTriggerTime = System.currentTimeMillis()
                }
            } else {
                event.changes.forEach { it.consume() }
            }
        }
    }
}

fun Modifier.safeHorizontalSwipe(
    onDrag: (Float) -> Unit,
    onDragEnd: (Float) -> Unit
): Modifier = this.pointerInput(Unit) {
    var totalDragX = 0f
    var totalDragY = 0f
    var isHorizontalDrag = false
    var dragStarted = false

    detectDragGestures(
        onDragStart = {
            totalDragX = 0f
            totalDragY = 0f
            isHorizontalDrag = false
            dragStarted = false
        },
        onDrag = { change, dragAmount ->
            totalDragX += dragAmount.x
            totalDragY += dragAmount.y

            if (!dragStarted) {
                if (abs(totalDragX) > 15f || abs(totalDragY) > 15f) {
                    dragStarted = true
                    if (abs(totalDragX) > abs(totalDragY) * 1.8f) {
                        isHorizontalDrag = true
                    }
                }
            }

            if (isHorizontalDrag) {
                change.consume()
                onDrag(dragAmount.x)
            }
        },
        onDragEnd = {
            if (isHorizontalDrag) {
                onDragEnd(totalDragX)
            }
        },
        onDragCancel = {
            if (isHorizontalDrag) {
                onDragEnd(0f)
            }
        }
    )
}

// ==========================================
// 2. 语音指令管理器 (延迟加载，不抢启动资源)
// ==========================================
class VoiceCommandManager(
    private val context: Context,
    private val onCommand: (String) -> Unit,
    private val onWake: () -> Unit,
    private val onError: (String) -> Unit = {}
) {
    private var keywordSpotter: KeywordSpotter? = null
    private var recognizer: OfflineRecognizer? = null
    private var audioRecord: AudioRecord? = null
    var currentState by mutableStateOf(VoiceState.IDLE)
    private val sampleRate = 16000
    private val frameSize = 480
    private val gain = 10.0f
    private val audioBuffer = mutableListOf<Short>()
    private val scope = CoroutineScope(Dispatchers.Main + SupervisorJob())
    private var recordingJob: Job? = null
    private var asrJob: Job? = null
    private var isEngineReady = false
    private var startAfterEngineReady = false
    private var speechStarted = false
    private var silenceMs = 0
    private var recordingMs = 0
    private val minRecordMs = 500
    private val maxRecordMs = 8000
    private val endSilenceMs = 900
    private val vadThreshold = 0.018f

    init {
        scope.launch(Dispatchers.IO) {
            try {
                delay(3500)
                val kwsConfig = KeywordSpotterConfig(
                    modelConfig = OnlineModelConfig(
                        transducer = OnlineTransducerModelConfig("kws/kws_encoder.onnx", "kws/kws_decoder.onnx", "kws/kws_joiner.onnx"),
                        tokens = "kws/kws_tokens.txt", numThreads = 1, debug = false
                    ),
                    keywordsFile = "kws/keywords.txt", keywordsScore = 4.0f, keywordsThreshold = 0.01f
                )
                keywordSpotter = KeywordSpotter(context.assets, kwsConfig)
                val asrConfig = OfflineRecognizerConfig(modelConfig = OfflineModelConfig(paraformer = OfflineParaformerModelConfig("asr/asr_model.onnx"), tokens = "asr/asr_tokens.txt", numThreads = 1, debug = false))
                recognizer = OfflineRecognizer(context.assets, asrConfig)
                isEngineReady = true
                withContext(Dispatchers.Main) { if (startAfterEngineReady) { startAfterEngineReady = false; start() } }
            } catch (e: Exception) { withContext(Dispatchers.Main) { onError("语音引擎加载失败") } }
        }
    }

    @SuppressLint("MissingPermission")
    fun start() {
        if (!isEngineReady) { startAfterEngineReady = true; return }
        if (recordingJob?.isActive == true) return
        val minBuf = AudioRecord.getMinBufferSize(sampleRate, AudioFormat.CHANNEL_IN_MONO, AudioFormat.ENCODING_PCM_16BIT)
        if (minBuf <= 0) return
        val recorder = AudioRecord(MediaRecorder.AudioSource.VOICE_RECOGNITION, sampleRate, AudioFormat.CHANNEL_IN_MONO, AudioFormat.ENCODING_PCM_16BIT, maxOf(minBuf * 2, frameSize * 4))
        if (recorder.state != AudioRecord.STATE_INITIALIZED) { recorder.release(); return }
        audioRecord = recorder
        try { recorder.startRecording() } catch (e: Exception) { recorder.release(); audioRecord = null; return }

        recordingJob = scope.launch(Dispatchers.IO) {
            val frame = ShortArray(frameSize)
            var stream = keywordSpotter?.createStream()
            while (isActive) {
                val read = recorder.read(frame, 0, frame.size)
                if (read <= 0) continue
                val floatFrame = FloatArray(read) { i -> ((frame[i] / 32768.0f) * gain).coerceIn(-1.0f, 1.0f) }

                when (currentState) {
                    VoiceState.IDLE, VoiceState.SUCCESS_TIP -> {
                        if (stream == null) stream = keywordSpotter?.createStream()
                        stream?.acceptWaveform(floatFrame, sampleRate)
                        if (stream != null && keywordSpotter?.isReady(stream!!) == true) {
                            keywordSpotter?.decode(stream!!)
                            if (!keywordSpotter?.getResult(stream!!)?.keyword.isNullOrBlank()) {
                                withContext(Dispatchers.Main) { beginRecording() }
                                stream = keywordSpotter?.createStream()
                            }
                        }
                    }
                    VoiceState.RECORDING -> {
                        synchronized(audioBuffer) { for (i in 0 until read) audioBuffer.add(frame[i]) }
                        val frameMs = read * 1000 / sampleRate
                        recordingMs += frameMs
                        val rms = calcRms(floatFrame)
                        if (rms > vadThreshold) { speechStarted = true; silenceMs = 0 } else if (speechStarted) silenceMs += frameMs
                        if ((speechStarted && recordingMs >= minRecordMs && silenceMs >= endSilenceMs) || recordingMs >= maxRecordMs) {
                            withContext(Dispatchers.Main) { executeAsr() }
                        }
                    }
                    VoiceState.RECOGNIZING -> {}
                }
            }
        }
    }

    private fun beginRecording() {
        if (!isEngineReady) { startAfterEngineReady = true; return }
        if (recordingJob?.isActive != true) start()
        if (currentState == VoiceState.RECOGNIZING) return
        synchronized(audioBuffer) { audioBuffer.clear() }
        speechStarted = false; silenceMs = 0; recordingMs = 0
        onWake(); currentState = VoiceState.RECORDING
    }

    private fun calcRms(samples: FloatArray): Float {
        if (samples.isEmpty()) return 0f
        var sum = 0f; for (s in samples) sum += s * s
        return sqrt(sum / samples.size)
    }

    private fun executeAsr() {
        if (currentState != VoiceState.RECORDING) return
        if (asrJob?.isActive == true) return
        val samples = synchronized(audioBuffer) { val data = audioBuffer.toShortArray(); audioBuffer.clear(); data }
        if (samples.size < sampleRate / 4) { currentState = VoiceState.IDLE; onCommand(""); return }

        currentState = VoiceState.RECOGNIZING
        asrJob = scope.launch(Dispatchers.IO) {
            try {
                val asr = recognizer
                if (asr == null) { withContext(Dispatchers.Main) { onCommand(""); currentState = VoiceState.IDLE }; return@launch }
                val asrStream = asr.createStream()
                val floatSamples = FloatArray(samples.size) { i -> ((samples[i] / 32768.0f) * gain).coerceIn(-1.0f, 1.0f) }
                asrStream.acceptWaveform(floatSamples, sampleRate); asr.decode(asrStream)
                val result = asr.getResult(asrStream).text.orEmpty().trim()
                withContext(Dispatchers.Main) {
                    onCommand(result); currentState = VoiceState.SUCCESS_TIP
                    delay(2500); if (currentState == VoiceState.SUCCESS_TIP) currentState = VoiceState.IDLE
                }
            } catch (e: Exception) { withContext(Dispatchers.Main) { onCommand(""); currentState = VoiceState.IDLE } }
        }
    }

    fun startManualRecording() {
        if (!isEngineReady) { startAfterEngineReady = true; return }
        if (recordingJob?.isActive != true) start()
        if (currentState == VoiceState.IDLE || currentState == VoiceState.SUCCESS_TIP) beginRecording()
    }
    fun stopManualRecordingAndRecognize() { if (currentState == VoiceState.RECORDING) executeAsr() }
    fun stop() { recordingJob?.cancel(); recordingJob = null; try { audioRecord?.stop(); audioRecord?.release() } catch (_: Exception) {}; audioRecord = null; if (currentState != VoiceState.RECOGNIZING) currentState = VoiceState.IDLE }
    fun release() { stop(); asrJob?.cancel(); scope.cancel() }
}

// ==========================================
// 3. 后台播放前台服务 (保活防护)
// ==========================================
class MusicPlaybackService : Service() {
    private val CHANNEL_ID = "qwe_music_playback_channel"
    private val NOTIFICATION_ID = 8899

    override fun onCreate() {
        super.onCreate()
        createNotificationChannel()
    }

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        val title = intent?.getStringExtra("title") ?: "QwePlayer"
        val artist = intent?.getStringExtra("artist") ?: "本地音乐"
        val isPlaying = intent?.getBooleanExtra("isPlaying", false) ?: false

        val notification = buildNotification(title, artist, isPlaying)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
            startForeground(NOTIFICATION_ID, notification, ServiceInfo.FOREGROUND_SERVICE_TYPE_MEDIA_PLAYBACK)
        } else {
            startForeground(NOTIFICATION_ID, notification)
        }
        return START_STICKY
    }

    private fun createNotificationChannel() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            val chan = NotificationChannel(CHANNEL_ID, "Qwe音频服务", NotificationManager.IMPORTANCE_LOW)
            chan.lockscreenVisibility = Notification.VISIBILITY_PUBLIC
            val manager = getSystemService(NOTIFICATION_SERVICE) as NotificationManager
            manager.createNotificationChannel(chan)
        }
    }

    private fun buildNotification(title: String, artist: String, isPlaying: Boolean): Notification {
        val mainIntent = Intent(this, MainActivity::class.java)
        val pendingIntent = PendingIntent.getActivity(this, 0, mainIntent, PendingIntent.FLAG_UPDATE_CURRENT or PendingIntent.FLAG_IMMUTABLE)

        return NotificationCompat.Builder(this, CHANNEL_ID)
            .setContentTitle(title)
            .setContentText(artist)
            .setSmallIcon(android.R.drawable.sym_def_app_icon)
            .setContentIntent(pendingIntent)
            .setOngoing(isPlaying)
            .setCategory(NotificationCompat.CATEGORY_SERVICE)
            .setVisibility(NotificationCompat.VISIBILITY_PUBLIC)
            .build()
    }

    override fun onBind(intent: Intent?): IBinder? = null
}

// ==========================================
// 4. ViewModel (控制中心 - 语义感知与极速队列)
// ==========================================
class MusicViewModel(application: Application) : AndroidViewModel(application) {
    private val context = application.applicationContext
    var exoPlayer: ExoPlayer? = null
    private var mediaSession: MediaSession? = null
    var voiceManager: VoiceCommandManager? = null
    private val prefs = context.getSharedPreferences("qwe_settings", Context.MODE_PRIVATE)

    var themeMode by mutableStateOf(prefs.getInt("theme", 0))
    var lrcLineHeight by mutableStateOf(prefs.getFloat("lrcLineHeight", 1.4f))
    var lrcAlpha by mutableStateOf(prefs.getFloat("lrcAlpha", 0.35f))
    var lrcSize by mutableStateOf(prefs.getFloat("lrcSize", 32f))
    var lrcSpacing by mutableStateOf(prefs.getFloat("lrcSpacing", 14f))
    var lrcFont by mutableStateOf(prefs.getInt("lrcFont", 0))
    var autoResumePlay by mutableStateOf(prefs.getBoolean("autoResumePlay", true))
    var keepScreenOn by mutableStateOf(prefs.getBoolean("keepScreenOn", true))
    var defaultShowPlaylist by mutableStateOf(prefs.getBoolean("defaultShowPlaylist", false))
    var defaultPlaylist by mutableStateOf(prefs.getString("defaultPlaylist", "") ?: "")
    val excludePlaylistNames = mutableStateListOf<String>().apply { addAll(prefs.getStringSet("excludePlaylistNames", emptySet()) ?: emptySet()) }
    var unifiedLoudness by mutableStateOf(prefs.getBoolean("unifiedLoudness", false))

    var eqEnabled by mutableStateOf(prefs.getBoolean("eqEnabled", false))
    var eqPreset by mutableStateOf(prefs.getInt("eqPreset", 0))
    var bassBoostStrength by mutableStateOf(prefs.getInt("bassBoost", 0))
    var reverbPreset by mutableStateOf(prefs.getInt("reverbPreset", 0))
    var virtualizerStrength by mutableStateOf(prefs.getInt("virtualizer", 0))
    val eqBandLevels = mutableStateListOf<Short>()

    private var equalizer: Equalizer? = null
    private var bassBoost: BassBoost? = null
    private var presetReverb: PresetReverb? = null
    private var virtualizer: Virtualizer? = null

    var duplicateSongsToResolve by mutableStateOf<List<Song>>(emptyList())
    var duplicateSelectionCountdown by mutableStateOf(8)
    private var selectionCountdownJob: Job? = null
    private var selectionResolutionCallback: ((Song) -> Unit)? = null

    var rawLyricsText by mutableStateOf("")

    data class EqPreset(val name: String, val gains: ShortArray)
    val eqPresets = listOf(
        EqPreset("普通", shortArrayOf(0, 0, 0, 0, 0, 0, 0, 0, 0, 0)),
        EqPreset("流行", shortArrayOf(2, 4, 6, 4, 0, -2, -2, 0, 2, 4)),
        EqPreset("摇滚", shortArrayOf(6, 4, 2, 0, -2, 0, 2, 4, 6, 6)),
        EqPreset("古典", shortArrayOf(4, 2, 0, -2, -4, -2, 0, 2, 4, 6)),
        EqPreset("爵士", shortArrayOf(2, 2, 0, 2, 0, 2, 4, 4, 2, 2)),
        EqPreset("人声", shortArrayOf(-2, -1, 0, 2, 4, 4, 3, 2, 1, 0)),
        EqPreset("重低音", shortArrayOf(8, 7, 6, 4, 2, 0, 0, 0, 0, 0)),
        EqPreset("舞曲", shortArrayOf(6, 5, 4, 2, 0, 0, 2, 4, 5, 6)),
        EqPreset("舒缓", shortArrayOf(2, 1, 0, -1, -2, -2, -1, 0, 1, 2)),
        EqPreset("现场", shortArrayOf(4, 3, 2, 1, 0, 0, 1, 2, 3, 4))
    )

    val reverbPresets = listOf("无", "小型房间", "中型房间", "大型房间", "大厅", "地下室", "山洞")
    val eqBandFrequencies = mutableListOf<Int>()

    var sleepTimerMinutes by mutableStateOf(0)
    var sleepTimerRemaining by mutableStateOf(0L)
    private var sleepTimerJob: Job? = null

    val playHistory = mutableStateListOf<Song>()
    var totalListenTimeMs by mutableStateOf(prefs.getLong("totalListenTime", 0L))
    var todayListenTimeMs by mutableStateOf(0L)
    private var lastListenDate by mutableStateOf(prefs.getString("lastListenDate", "") ?: "")
    private var lastPlayPos = 0L

    private var lastSongId = prefs.getLong("lastSongId", -1L)
    fun getCurrentPosition(): Long = exoPlayer?.currentPosition ?: 0L

    var songList by mutableStateOf<List<Song>>(emptyList())
    var currentQueue by mutableStateOf<List<Song>>(emptyList())
    var playlists by mutableStateOf<List<CustomPlaylist>>(emptyList())
    var currentSong by mutableStateOf<Song?>(null)
    var nextSong by mutableStateOf<Song?>(null)
    var voiceQueue by mutableStateOf<List<Song>>(emptyList())
    var requestedTab by mutableStateOf<String?>(null)
    var currentLyrics by mutableStateOf<List<LrcRow>>(emptyList())
    var isPlaying by mutableStateOf(false)
    var isScanning by mutableStateOf(false)
    var playMode by mutableStateOf(PlayMode.SHUFFLE)
    var voiceFeedback by mutableStateOf("")

    private var dynamicsProcessing: DynamicsProcessing? = null
    private var currentAudioSessionId: Int = C.AUDIO_SESSION_ID_UNSET

    val favoriteSongIds = mutableStateMapOf<Long, Boolean>()

    private var wasPlayingBeforeVoice = false
    private var fadeJob: Job? = null

    val playlistDir: File by lazy {
        val publicDir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_MUSIC)
        val testFile = File(publicDir, ".qwe_write_test")
        val canWrite = try {
            if (!publicDir.exists()) publicDir.mkdirs()
            testFile.createNewFile() && testFile.delete()
        } catch (_: Exception) { false }
        if (canWrite) publicDir else (context.getExternalFilesDir(Environment.DIRECTORY_MUSIC) ?: context.filesDir)
    }

    val FAVORITE_PLAYLIST_NAME = "最爱"
    private var lrcJob: Job? = null

    init {
        val attr = AudioAttributes.Builder().setUsage(C.USAGE_MEDIA).setContentType(C.AUDIO_CONTENT_TYPE_MUSIC).build()
        exoPlayer = ExoPlayer.Builder(context).setAudioAttributes(attr, true).setHandleAudioBecomingNoisy(true).build().apply {
            shuffleModeEnabled = true; repeatMode = Player.REPEAT_MODE_ALL
            addListener(object : Player.Listener {
                override fun onIsPlayingChanged(p: Boolean) {
                    this@MusicViewModel.isPlaying = p
                    if (p) {
                        lastPlayPos = exoPlayer?.currentPosition ?: 0L
                    } else {
                        val currentPos = exoPlayer?.currentPosition ?: 0L
                        val delta = currentPos - lastPlayPos
                        if (delta > 0) updateListenTime(delta)
                    }
                    updateServiceState()
                }
                override fun onMediaItemTransition(m: MediaItem?, r: Int) {
                    val s = songList.find { s2: Song -> s2.uri == m?.localConfiguration?.uri }
                    if (s != null && currentSong != null && currentSong?.id != s.id) {
                        val currentPos = exoPlayer?.currentPosition ?: 0L
                        val delta = minOf(currentPos - lastPlayPos, currentSong?.duration ?: 0L)
                        if (delta > 30000L) addToHistory(currentSong!!)
                        if (delta > 0) updateListenTime(delta)
                    }
                    this@MusicViewModel.currentSong = s
                    s?.let { loadLyrics(it.dataPath) }
                    s?.let { addToHistory(it) }
                    lastPlayPos = 0L
                    updateNextSong()
                    updateServiceState()
                }
                override fun onEvents(player: Player, events: Player.Events) { updateNextSong() }
                override fun onPlayerError(error: PlaybackException) { nextMusic() }
                override fun onAudioSessionIdChanged(audioSessionId: Int) {
                    this@MusicViewModel.currentAudioSessionId = audioSessionId
                    applyLoudnessEffect()
                    initEqualizerBands()
                    applyAudioEffects()
                }
            })
        }
        mediaSession = MediaSession.Builder(context, exoPlayer!!).build()

        voiceManager = VoiceCommandManager(
            context = context,
            onWake = {
                wasPlayingBeforeVoice = exoPlayer?.isPlaying == true
                if (wasPlayingBeforeVoice) { fadeJob?.cancel(); exoPlayer?.pause() }
                voiceFeedback = "我在听，请吩咐..."
            },
            onCommand = { handleAsrResult(it) },
            onError = { voiceFeedback = it }
        )

        viewModelScope.launch {
            while(isActive) {
                if (isPlaying) {
                    val pos = exoPlayer?.currentPosition ?: 0L
                    prefs.edit().putLong("lastPos", pos).apply()
                    currentSong?.id?.let { prefs.edit().putLong("lastSongId", it).apply() }
                    if (lastPlayPos > 0 && pos > lastPlayPos) {
                        updateListenTime(pos - lastPlayPos)
                    }
                    lastPlayPos = pos
                }
                delay(5000)
            }
        }
    }

    fun toggleExcludePlaylist(name: String) {
        if (excludePlaylistNames.contains(name)) {
            excludePlaylistNames.remove(name)
        } else {
            excludePlaylistNames.add(name)
        }
        prefs.edit().putStringSet("excludePlaylistNames", HashSet(excludePlaylistNames)).apply()
        syncQueueIfInAllSongs()
    }

    private fun syncQueueIfInAllSongs() {
        val lastTab = prefs.getString("lastPlaylistTab", "全部歌曲") ?: "全部歌曲"
        if (lastTab == "全部歌曲") {
            val filtered = getFilteredAllSongs()
            currentQueue = filtered

            val player = exoPlayer ?: return
            val currentMediaId = currentSong?.id

            player.setMediaItems(filtered.map { MediaItem.fromUri(it.uri) })
            player.prepare()

            val newIndex = filtered.indexOfFirst { it.id == currentMediaId }
            if (newIndex != -1) {
                player.seekTo(newIndex, player.currentPosition)
            } else if (filtered.isNotEmpty()) {
                player.seekTo(0, 0L)
                currentSong = filtered.first()
                currentSong?.let { loadLyrics(it.dataPath) }
            }
            updateNextSong()
        }
    }

    fun getFilteredAllSongs(): List<Song> {
        if (excludePlaylistNames.isEmpty()) return songList
        val excludedIds = mutableSetOf<Long>()
        val excludedPaths = mutableSetOf<String>()

        for (name in excludePlaylistNames) {
            playlists.find { it.name == name }?.songs?.forEach {
                excludedIds.add(it.id)
                excludedPaths.add(it.dataPath)
            }
        }
        return if (excludedIds.isNotEmpty() || excludedPaths.isNotEmpty()) {
            songList.filter { it.id !in excludedIds && it.dataPath !in excludedPaths }
        } else {
            songList
        }
    }

    private fun updateServiceState() {
        val current = currentSong
        val serviceIntent = Intent(context, MusicPlaybackService::class.java).apply {
            putExtra("title", current?.title ?: "QwePlayer")
            putExtra("artist", current?.artist ?: "本地音乐")
            putExtra("isPlaying", isPlaying)
        }
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            context.startForegroundService(serviceIntent)
        } else {
            context.startService(serviceIntent)
        }
    }

    private fun updateNextSong() {
        val player = exoPlayer ?: return
        val nextIndex = player.nextMediaItemIndex
        nextSong = if (nextIndex != C.INDEX_UNSET) currentQueue.getOrNull(nextIndex) else null
    }

    fun isFavorite(song: Song?): Boolean {
        if (song == null) return false
        return favoriteSongIds[song.id] == true
    }

    fun toggleFavorite(song: Song?) {
        if (song == null) return
        val currentlyFav = favoriteSongIds[song.id] == true
        favoriteSongIds[song.id] = !currentlyFav

        viewModelScope.launch(Dispatchers.IO) {
            var favoritePlaylist = playlists.find { playlist: CustomPlaylist -> playlist.name == FAVORITE_PLAYLIST_NAME }
            if (favoritePlaylist == null) {
                try {
                    if (!playlistDir.exists()) playlistDir.mkdirs()
                    val file = File(playlistDir, "$FAVORITE_PLAYLIST_NAME.m3u")
                    if (!file.exists()) file.createNewFile()
                    val newP = CustomPlaylist(FAVORITE_PLAYLIST_NAME, file, emptyList())
                    withContext(Dispatchers.Main) { playlists = listOf(newP) + playlists }
                    favoritePlaylist = newP
                } catch (e: Exception) {
                    withContext(Dispatchers.Main) { favoriteSongIds[song.id] = currentlyFav }
                    return@launch
                }
            }

            val p = favoritePlaylist ?: return@launch
            if (currentlyFav) {
                val updatedSongs = p.songs.filter { s -> s.id != song.id }
                if (writePlaylistSafely(p, updatedSongs)) {
                    withContext(Dispatchers.Main) {
                        playlists = playlists.map { element ->
                            if (element.name == p.name) p.copy(songs = updatedSongs) else element
                        }
                    }
                }
            } else {
                if (appendPlaylistSafely(p, song)) {
                    withContext(Dispatchers.Main) {
                        playlists = playlists.map { element ->
                            if (element.name == p.name) p.copy(songs = p.songs + song) else element
                        }
                    }
                }
            }
        }
    }

    private fun readM3uSongs(file: File, songByPath: Map<String, Song>, songByFilename: Map<String, Song>): List<Song> {
        return try {
            file.readLines()
                .asSequence()
                .map { it.trim().replace("\r", "") }
                .filter { it.isNotEmpty() && !it.startsWith("#") }
                .mapNotNull { line ->
                    var path = line
                    if (path.startsWith("file://", ignoreCase = true)) path = path.substring(7)
                    else if (path.startsWith("file:", ignoreCase = true)) path = path.substring(5)

                    if (path.contains("%") || path.contains("+")) {
                        try { path = URLDecoder.decode(path.replace("+", "%2B"), "UTF-8") } catch (_: Exception) {}
                    }
                    path = path.replace("\\", "/").trim()
                    songByPath[path] ?: songByFilename[path.substringAfterLast("/").lowercase()]
                }
                .toList()
        } catch (e: Exception) {
            emptyList()
        }
    }

    private fun writePlaylistSafely(p: CustomPlaylist, songs: List<Song>): Boolean = try {
        p.file.parentFile?.mkdirs()
        p.file.writeText(songs.joinToString("\n") { s: Song -> s.dataPath } + if (songs.isNotEmpty()) "\n" else "")
        true
    } catch (e: Exception) { false }

    private fun appendPlaylistSafely(p: CustomPlaylist, song: Song): Boolean = try {
        p.file.parentFile?.mkdirs()
        p.file.appendText("${song.dataPath}\n")
        true
    } catch (e: Exception) { false }

    fun renamePlaylist(oldPlaylist: CustomPlaylist, newName: String) {
        val safeName = newName.trim()
        if (safeName.isEmpty() || playlists.any { it.name == safeName }) return
        try {
            val newFile = File(playlistDir, "$safeName.m3u")
            if (oldPlaylist.file.renameTo(newFile)) {
                playlists = playlists.map { if (it.name == oldPlaylist.name) it.copy(name = safeName, file = newFile) else it }
                if (excludePlaylistNames.contains(oldPlaylist.name)) {
                    excludePlaylistNames.remove(oldPlaylist.name)
                    excludePlaylistNames.add(safeName)
                    prefs.edit().putStringSet("excludePlaylistNames", HashSet(excludePlaylistNames)).apply()
                    syncQueueIfInAllSongs()
                }
            }
        } catch (e: Exception) {
            voiceFeedback = "重命名失败"
        }
    }

    fun deletePlaylist(p: CustomPlaylist) {
        if (p.name == FAVORITE_PLAYLIST_NAME) return
        try {
            if (p.file.delete()) {
                playlists = playlists.filter { it.name != p.name }
                if (excludePlaylistNames.contains(p.name)) {
                    excludePlaylistNames.remove(p.name)
                    prefs.edit().putStringSet("excludePlaylistNames", HashSet(excludePlaylistNames)).apply()
                    syncQueueIfInAllSongs()
                }
            }
        } catch (e: Exception) {
            voiceFeedback = "删除列表失败"
        }
    }

    fun deleteLocalSong(song: Song) {
        try {
            val file = File(song.dataPath)
            var deleted = false
            if (file.exists() && file.delete()) deleted = true
            context.contentResolver.delete(song.uri, null, null)
            if (!deleted && !file.exists()) deleted = true

            if (deleted) {
                songList = songList.filter { it.id != song.id }
                if (currentSong?.id == song.id) nextMusic()
                voiceFeedback = "已删除: ${song.title}"
            } else {
                voiceFeedback = "删除失败，可能受系统权限限制"
            }
        } catch(e: Exception) {
            voiceFeedback = "删除异常: ${e.message}"
        }
    }

    fun moveSongInPlaylist(p: CustomPlaylist, song: Song, offset: Int) {
        val index = p.songs.indexOfFirst { s: Song -> s.id == song.id }; if (index == -1) return
        val newIndex = (index + offset).coerceIn(0, p.songs.lastIndex); if (index == newIndex) return
        val mutable = p.songs.toMutableList(); val item = mutable.removeAt(index); mutable.add(newIndex, item)
        if (!writePlaylistSafely(p, mutable)) return
        val updated = p.copy(songs = mutable)
        playlists = playlists.map { element: CustomPlaylist -> if (element.name == p.name) updated else element }
        if (currentQueue == p.songs) { currentQueue = mutable; exoPlayer?.setMediaItems(mutable.map { s: Song -> MediaItem.fromUri(s.uri) }); exoPlayer?.prepare() }
    }

    fun removeSongFromM3uPlaylist(p: CustomPlaylist, song: Song) {
        val updatedSongs = p.songs.filter { s: Song -> s.id != song.id }
        if (!writePlaylistSafely(p, updatedSongs)) return
        val updated = p.copy(songs = updatedSongs)
        playlists = playlists.map { element: CustomPlaylist -> if (element.name == p.name) updated else element }
        if (currentQueue == p.songs) { currentQueue = updatedSongs; exoPlayer?.setMediaItems(updatedSongs.map { s: Song -> MediaItem.fromUri(s.uri) }); exoPlayer?.prepare() }
    }

    private fun readPlaylistsSync(songs: List<Song>): List<CustomPlaylist> {
        val list = mutableListOf<CustomPlaylist>()
        val dirsToScan = listOfNotNull(
            Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_MUSIC),
            context.getExternalFilesDir(Environment.DIRECTORY_MUSIC),
            context.filesDir
        ).distinct()

        val songByPath = songs.associateBy { it.dataPath }
        val songByFilename = songs.associateBy { it.dataPath.substringAfterLast("/").lowercase() }

        for (dir in dirsToScan) {
            if (!dir.exists()) dir.mkdirs()
            val files: Array<File>? = dir.listFiles()
            if (files != null) {
                for (file in files) {
                    if (file.isFile && (file.extension.equals("m3u", ignoreCase = true) || file.extension.equals("m3u8", ignoreCase = true))) {
                        val name = file.nameWithoutExtension
                        if (list.none { it.name == name }) {
                            list.add(CustomPlaylist(name, file, readM3uSongs(file, songByPath, songByFilename)))
                        }
                    }
                }
            }
        }

        list.sortWith(Comparator { p1: CustomPlaylist, p2: CustomPlaylist ->
            val isFav1 = if (p1.name == FAVORITE_PLAYLIST_NAME) 0 else 1
            val isFav2 = if (p1.name == FAVORITE_PLAYLIST_NAME) 0 else 1
            if (isFav1 != isFav2) isFav1.compareTo(isFav2) else p1.name.compareTo(p2.name)
        })

        return list
    }

    fun createPlaylist(name: String) {
        val safeName = name.trim(); if (safeName.isBlank()) return
        try {
            if (!playlistDir.exists()) playlistDir.mkdirs()
            val file = File(playlistDir, "$safeName.m3u")
            if (!file.exists()) file.createNewFile()
            viewModelScope.launch(Dispatchers.IO) {
                val updated = readPlaylistsSync(songList)
                withContext(Dispatchers.Main) { playlists = updated }
            }
        } catch (e: Exception) { voiceFeedback = "无法创建播放列表" }
    }

    fun addSongToPlaylist(p: CustomPlaylist, s: Song) {
        if (p.songs.any { it.id == s.id }) return
        if (appendPlaylistSafely(p, s)) {
            val updated = p.copy(songs = p.songs + s)
            playlists = playlists.map { if (it.name == p.name) updated else it }
            if (p.name == FAVORITE_PLAYLIST_NAME) favoriteSongIds[s.id] = true
        }
    }

    fun removeSongFromPlaylist(p: CustomPlaylist, s: Song) {
        val updatedSongs = p.songs.filter { i -> i.id != s.id }
        if (writePlaylistSafely(p, updatedSongs)) {
            val updated = p.copy(songs = updatedSongs)
            playlists = playlists.map { if (it.name == p.name) updated else it }
            if (p.name == FAVORITE_PLAYLIST_NAME) favoriteSongIds.remove(s.id)
        }
    }

    fun togglePlayPause() { if (isPlaying) pauseMusic() else resumeMusic() }
    fun pauseMusic() { fadeJob?.cancel(); fadeJob = viewModelScope.launch { for (i in 10 downTo 0) { exoPlayer?.volume = i / 10f; delay(15) }; exoPlayer?.pause(); isPlaying = false; exoPlayer?.volume = 1f } }
    fun resumeMusic() { fadeJob?.cancel(); isPlaying = true; fadeJob = viewModelScope.launch { exoPlayer?.volume = 0f; exoPlayer?.play(); for (i in 1..10) { exoPlayer?.volume = i / 10f; delay(15) }; exoPlayer?.volume = 1f } }
    fun nextMusic() { fadeJob?.cancel(); fadeJob = viewModelScope.launch { for (i in 10 downTo 0) { exoPlayer?.volume = i / 10f; delay(15) }; exoPlayer?.seekToNext(); exoPlayer?.play(); for (i in 1..10) { exoPlayer?.volume = i / 10f; delay(15) }; exoPlayer?.volume = 1f } }
    fun prevMusic() { fadeJob?.cancel(); fadeJob = viewModelScope.launch { for (i in 10 downTo 0) { exoPlayer?.volume = i / 10f; delay(15) }; exoPlayer?.seekToPrevious(); exoPlayer?.play(); for (i in 1..10) { exoPlayer?.volume = i / 10f; delay(15) }; exoPlayer?.volume = 1f } }

    fun playSong(song: Song, queue: List<Song>, tabName: String? = null) {
        if (tabName != null) prefs.edit().putString("lastPlaylistTab", tabName).apply()
        fadeJob?.cancel()
        fadeJob = viewModelScope.launch {
            if (isPlaying) { for (i in 10 downTo 0) { exoPlayer?.volume = i / 10f; delay(15) } }
            exoPlayer?.volume = 0f

            var targetQueue = queue
            var index = targetQueue.indexOfFirst { s: Song -> s.id == song.id }

            if (index == -1) {
                targetQueue = listOf(song)
                index = 0
            }

            if (currentQueue != targetQueue) {
                currentQueue = targetQueue
                exoPlayer?.setMediaItems(targetQueue.map { s: Song -> MediaItem.fromUri(s.uri) })
                exoPlayer?.prepare()
            }

            exoPlayer?.seekTo(index, 0L)
            exoPlayer?.play()
            updateNextSong()

            for (i in 1..10) { exoPlayer?.volume = i / 10f; delay(15) }
            exoPlayer?.volume = 1f
        }
    }

    fun updateSetting(key: String, value: Any) {
        when (value) {
            is Int -> { prefs.edit().putInt(key, value).apply(); if (key == "theme") themeMode = value; if (key == "lrcFont") lrcFont = value }
            is String -> {
                prefs.edit().putString(key, value).apply()
                if (key == "defaultPlaylist") defaultPlaylist = value
            }
            is Boolean -> {
                prefs.edit().putBoolean(key, value).apply()
                if (key == "autoResumePlay") autoResumePlay = value
                if (key == "defaultShowPlaylist") defaultShowPlaylist = value
                if (key == "keepScreenOn") keepScreenOn = value
                if (key == "unifiedLoudness") {
                    unifiedLoudness = value
                    applyLoudnessEffect()
                }
            }
            is Float -> { prefs.edit().putFloat(key, value).apply(); when (key) { "lrcAlpha" -> lrcAlpha = value; "lrcSize" -> lrcSize = value; "lrcSpacing" -> lrcSpacing = value; "lrcLineHeight" -> lrcLineHeight = value } }
        }
    }

    private fun applyLoudnessEffect() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.P) return
        try { dynamicsProcessing?.release(); dynamicsProcessing = null } catch (_: Exception) {}

        val sessionId = currentAudioSessionId
        if (!unifiedLoudness || sessionId == C.AUDIO_SESSION_ID_UNSET || sessionId == 0) return

        try {
            val config = DynamicsProcessing.Config.Builder(0, 2, false, 0, true, 1, false, 0, false).build()
            val mbc = DynamicsProcessing.MbcBand(true, 20000f, 1200f, 3500f, 2.2f, -24f, 10f, -60f, 1f, 7.5f, 0f)
            config.setMbcBandAllChannelsTo(0, mbc)
            dynamicsProcessing = DynamicsProcessing(0, sessionId, config).apply { enabled = true }
        } catch (_: Exception) {}
    }

    fun initEqualizerBands() {
        try {
            val sessionId = currentAudioSessionId
            if (sessionId == C.AUDIO_SESSION_ID_UNSET || sessionId == 0) return
            val tempEq = Equalizer(0, sessionId)
            val numBands = tempEq.numberOfBands.toInt()
            eqBandFrequencies.clear()
            for (i in 0 until numBands) {
                eqBandFrequencies.add(tempEq.getCenterFreq(i.toShort()) / 1000)
            }
            if (eqBandLevels.isEmpty()) {
                val saved = loadCustomEqBands()
                if (saved != null && saved.size == numBands) {
                    eqBandLevels.addAll(saved.toList())
                } else {
                    eqBandLevels.addAll(ShortArray(numBands) { 0 }.toList())
                }
            }
            tempEq.release()
        } catch (_: Exception) {}
    }

    private fun loadCustomEqBands(): ShortArray? {
        return try {
            val count = prefs.getInt("eqBandCount", 0)
            if (count <= 0) return null
            val bands = ShortArray(count)
            for (i in 0 until count) bands[i] = prefs.getInt("eqBand_$i", 0).toShort()
            bands
        } catch (_: Exception) { null }
    }

    private fun saveCustomEqBands() {
        try {
            prefs.edit().putInt("eqBandCount", eqBandLevels.size).apply()
            eqBandLevels.forEachIndexed { index, value -> prefs.edit().putInt("eqBand_$index", value.toInt()).apply() }
        } catch (_: Exception) {}
    }

    fun applyAudioEffects() {
        val sessionId = currentAudioSessionId
        if (sessionId == C.AUDIO_SESSION_ID_UNSET || sessionId == 0) return

        try {
            equalizer?.release(); equalizer = null
            bassBoost?.release(); bassBoost = null
            presetReverb?.release(); presetReverb = null
            virtualizer?.release(); virtualizer = null
        } catch (_: Exception) {}

        if (!eqEnabled) return

        try {
            equalizer = Equalizer(0, sessionId).apply {
                enabled = true
                val numBands = numberOfBands.toInt()
                val gains = if (eqPreset == -1) eqBandLevels.toShortArray() else eqPresets.getOrNull(eqPreset)?.gains ?: shortArrayOf(0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
                for (i in 0 until minOf(numBands, gains.size)) setBandLevel(i.toShort(), gains[i])
            }
        } catch (_: Exception) { equalizer = null }

        try {
            if (bassBoostStrength > 0) bassBoost = BassBoost(0, sessionId).apply { enabled = true; setStrength(bassBoostStrength.toShort()) }
        } catch (_: Exception) { bassBoost = null }

        try {
            if (reverbPreset > 0) presetReverb = PresetReverb(0, sessionId).apply { enabled = true; preset = (reverbPreset - 1).toShort() }
        } catch (_: Exception) { presetReverb = null }

        try {
            if (virtualizerStrength > 0) virtualizer = Virtualizer(0, sessionId).apply { enabled = true; setStrength(virtualizerStrength.toShort()) }
        } catch (_: Exception) { virtualizer = null }
    }

    fun toggleEqEnabled(enabled: Boolean) {
        eqEnabled = enabled
        prefs.edit().putBoolean("eqEnabled", enabled).apply()
        applyAudioEffects()
    }

    fun applyEqPreset(index: Int) {
        eqPreset = index
        prefs.edit().putInt("eqPreset", index).apply()
        if (index >= 0 && index < eqPresets.size) {
            val gains = eqPresets[index].gains
            eqBandLevels.clear()
            eqBandLevels.addAll(gains.toList())
        }
        applyAudioEffects()
    }

    fun setVirtualizer(strength: Int) {
        virtualizerStrength = strength
        prefs.edit().putInt("virtualizer", strength).apply()
        applyAudioEffects()
    }

    fun updateReverbPreset(preset: Int) {
        reverbPreset = preset
        prefs.edit().putInt("reverbPreset", preset).apply()
        applyAudioEffects()
    }

    fun startSleepTimer(minutes: Int) {
        stopSleepTimer()
        if (minutes <= 0) return
        sleepTimerMinutes = minutes
        val totalMs = minutes * 60 * 1000L
        sleepTimerRemaining = totalMs

        sleepTimerJob = viewModelScope.launch {
            val startTime = System.currentTimeMillis()
            while (isActive && sleepTimerRemaining > 0) {
                delay(1000)
                val elapsed = System.currentTimeMillis() - startTime
                sleepTimerRemaining = (totalMs - elapsed).coerceAtLeast(0L)
            }
            if (sleepTimerRemaining <= 0L) {
                pauseMusic()
                sleepTimerMinutes = 0
                sleepTimerRemaining = 0L
            }
        }
    }

    fun stopSleepTimer() {
        sleepTimerJob?.cancel()
        sleepTimerJob = null
        sleepTimerMinutes = 0
        sleepTimerRemaining = 0L
    }

    fun formatSleepTime(ms: Long): String {
        val totalSec = ms / 1000
        val min = totalSec / 60
        val sec = totalSec % 60
        return "%02d:%02d".format(min, sec)
    }

    private fun getTodayDate(): String {
        val sdf = java.text.SimpleDateFormat("yyyy-MM-dd", java.util.Locale.getDefault())
        return sdf.format(java.util.Date())
    }

    private fun checkAndResetDaily() {
        val today = getTodayDate()
        if (lastListenDate != today) {
            todayListenTimeMs = 0L
            lastListenDate = today
            prefs.edit().putString("lastListenDate", today).apply()
        }
    }

    private fun addToHistory(song: Song) {
        val existingIndex = playHistory.indexOfFirst { it.id == song.id }
        if (existingIndex != -1) playHistory.removeAt(existingIndex)
        playHistory.add(0, song)
        if (playHistory.size > 100) playHistory.removeAt(playHistory.lastIndex)
    }

    private fun updateListenTime(deltaMs: Long) {
        if (deltaMs <= 0) return
        checkAndResetDaily()
        totalListenTimeMs += deltaMs
        todayListenTimeMs += deltaMs
        prefs.edit().putLong("totalListenTime", totalListenTimeMs).apply()
    }

    fun formatListenTime(ms: Long): String {
        val totalSec = ms / 1000
        val hours = totalSec / 3600
        val minutes = (totalSec % 3600) / 60
        return if (hours > 0) "${hours}小时${minutes}分钟" else "${minutes}分钟"
    }

    fun startPressTalk() = voiceManager?.startManualRecording()
    fun stopPressTalk() = voiceManager?.stopManualRecordingAndRecognize()

    fun presentSongSelection(matches: List<Song>, onResolved: (Song) -> Unit) {
        selectionCountdownJob?.cancel()
        duplicateSongsToResolve = matches
        duplicateSelectionCountdown = 8
        selectionResolutionCallback = onResolved
        selectionCountdownJob = viewModelScope.launch {
            while (duplicateSelectionCountdown > 0) {
                delay(1000)
                duplicateSelectionCountdown--
            }
            if (duplicateSongsToResolve.isNotEmpty()) {
                val bestFallback = duplicateSongsToResolve.first()
                selectionResolutionCallback?.invoke(bestFallback)
            }
            duplicateSongsToResolve = emptyList()
            selectionResolutionCallback = null
        }
    }

    fun selectDuplicateSong(song: Song) {
        selectionCountdownJob?.cancel()
        selectionResolutionCallback?.invoke(song)
        duplicateSongsToResolve = emptyList()
        selectionResolutionCallback = null
    }

    private fun findDuplicateSongMatches(clean: String): List<Song> {
        val searchList = songList

        val exact = searchList.filter { s -> s.title.lowercase() == clean }
        if (exact.isNotEmpty()) return exact

        val contain = searchList.filter { s ->
            s.title.lowercase().contains(clean) || s.artist.lowercase().contains(clean)
        }
        if (contain.isNotEmpty()) {
            return contain.sortedBy { abs(it.title.length - clean.length) }.take(5)
        }

        val matched = mutableListOf<Pair<Song, Int>>()
        for (song in searchList) {
            val dist = minOf(levenshteinDistance(clean, song.title.lowercase()), levenshteinDistance(clean, song.artist.lowercase()))
            val threshold = maxOf(1, clean.length / 4)
            if (dist <= threshold) {
                matched.add(song to dist)
            }
        }
        return matched.sortedBy { it.second }.map { it.first }.take(5)
    }

    private fun cleanVoiceInput(text: String): String {
        var t = text.lowercase().trim()
        val removePrefixes = listOf(
            "请给我", "给我", "帮我", "我要听", "我想听", "我要", "我想",
            "播放", "放一下", "放首", "放一首", "来一首", "来首", "来几首", "听一下",
            "听听", "听首", "听一首", "找一下", "搜索", "查找", "搜一下", "搜", "听"
        )
        for (prefix in removePrefixes) {
            if (t.startsWith(prefix)) {
                t = t.removePrefix(prefix)
            }
        }
        return t.replace("。", "").replace("，", "").replace("？", "").replace("！", "").replace(" ", "").trim()
    }

    private fun setVoiceQueueAndPlay(songs: List<Song>, initialSong: Song? = null, mode: PlayMode? = null, tabTitle: String = "语音队列") {
        if (songs.isEmpty()) return
        voiceQueue = songs
        currentQueue = songs
        exoPlayer?.setMediaItems(songs.map { s: Song -> MediaItem.fromUri(s.uri) })
        exoPlayer?.prepare()

        if (mode != null) {
            switchPlayMode(mode)
        }

        val playTarget = initialSong ?: if (mode == PlayMode.SHUFFLE) songs.random() else songs.first()
        val index = songs.indexOfFirst { it.id == playTarget.id }.coerceAtLeast(0)
        exoPlayer?.seekTo(index, 0L)
        exoPlayer?.play()
        currentSong = playTarget
        currentSong?.let { loadLyrics(it.dataPath) }
        updateNextSong()

        requestedTab = tabTitle
        prefs.edit().putString("lastPlaylistTab", tabTitle).apply()
    }

    private fun appendSongToVoiceQueue(song: Song) {
        val merged = (voiceQueue + song).distinctBy { it.id }
        voiceQueue = merged
        currentQueue = merged
        exoPlayer?.setMediaItems(merged.map { MediaItem.fromUri(it.uri) })
        exoPlayer?.prepare()
        updateNextSong()
        requestedTab = "语音队列"
    }

    private fun findSongsByArtistRobust(artistKeyword: String): List<Song> {
        val clean = cleanVoiceInput(artistKeyword).replace("的歌", "").replace("歌曲", "")
        if (clean.isBlank()) return emptyList()

        val matched = songList.filter { ArtistAliasEngine.isArtistMatch(clean, it.artist) }
        if (matched.isNotEmpty()) return matched

        val pinyinMatches = songList.filter { s ->
            val pinyinInitial = s.artist.map { getInitialLetter(it.toString()) }.joinToString("").lowercase()
            pinyinInitial.contains(clean)
        }
        if (pinyinMatches.isNotEmpty()) return pinyinMatches

        val fuzzyMatches = mutableListOf<Pair<Song, Int>>()
        for (s in songList) {
            val dist = levenshteinDistance(clean, s.artist.lowercase())
            if (dist <= maxOf(1, clean.length / 3)) {
                fuzzyMatches.add(s to dist)
            }
        }
        return fuzzyMatches.sortedBy { it.second }.map { it.first }
    }

    private fun findSongsByTitleRobust(titleKeyword: String): List<Song> {
        val clean = cleanVoiceInput(titleKeyword)
        if (clean.isBlank()) return emptyList()
        val exact = songList.filter { it.title.lowercase() == clean }
        if (exact.isNotEmpty()) return exact

        val contains = songList.filter { it.title.lowercase().contains(clean) }
        if (contains.isNotEmpty()) return contains

        return songList.filter { levenshteinDistance(clean, it.title.lowercase()) <= maxOf(1, clean.length / 3) }
    }

    // ==========================================
    // 智能语音中枢调度（包含中英文艺人多场景匹配）
    // ==========================================
    private fun handleAsrResult(text: String) {
        val raw = text.trim()
        val clean = cleanVoiceInput(raw)
        if (clean.isEmpty() && !raw.contains("下一首") && !raw.contains("上一首") && !raw.contains("暂停") && !raw.contains("继续")) {
            voiceFeedback = "没听清，请再说一遍"
            if (wasPlayingBeforeVoice) resumeMusic()
            wasPlayingBeforeVoice = false
            return
        }

        val allKnownArtists = songList.map { it.artist.trim() }.filter { it.isNotBlank() && it != "未知" }.distinct()
        val matchedArtist = allKnownArtists.find { artist ->
            ArtistAliasEngine.isArtistMatch(clean, artist) ||
                    ArtistAliasEngine.isArtistMatch(raw, artist) ||
                    raw.contains(artist, ignoreCase = true) ||
                    clean.contains(artist.lowercase())
        }

        val isSingleLoopIntent = raw.contains("单曲") || raw.contains("单曲循环") || raw.contains("一直放") || raw.contains("重复放")
        val isShuffleIntent = raw.contains("随机") || raw.contains("随便") || raw.contains("乱序")

        when {
            raw.contains("切换到曲库") || raw.contains("全部歌曲") || raw.contains("待播放") -> {
                requestedTab = "全部歌曲"; voiceFeedback = "已切换到全部歌曲"; if(wasPlayingBeforeVoice) resumeMusic()
            }
            raw.contains("切换到收藏") || raw.contains("最爱") || raw.contains("我喜欢") -> {
                requestedTab = FAVORITE_PLAYLIST_NAME; voiceFeedback = "已切换到收藏"; if(wasPlayingBeforeVoice) resumeMusic()
            }
            raw.contains("切换到语音") || raw.contains("语音队列") -> {
                requestedTab = "语音队列"; voiceFeedback = "已切换到语音队列"; if(wasPlayingBeforeVoice) resumeMusic()
            }
            raw.contains("收藏这首") || raw.contains("喜欢这首") || raw.contains("加入最爱") || raw.contains("加到收藏") -> {
                currentSong?.let { if (!isFavorite(it)) toggleFavorite(it) }
                voiceFeedback = "已为你收藏当前歌曲"
                if (wasPlayingBeforeVoice) resumeMusic()
            }
            raw.contains("取消收藏") || raw.contains("不喜欢这首") || raw.contains("移出最爱") -> {
                currentSong?.let { if (isFavorite(it)) toggleFavorite(it) }
                voiceFeedback = "已从收藏中移除"
                if (wasPlayingBeforeVoice) resumeMusic()
            }
            raw.contains("大声") || raw.contains("调大") || raw.contains("大一点") -> {
                adjustVol(true); voiceFeedback = "已调大音量"; if(wasPlayingBeforeVoice) resumeMusic()
            }
            raw.contains("小声") || raw.contains("调小") || raw.contains("轻一点") || raw.contains("小一点") -> {
                adjustVol(false); voiceFeedback = "已调小音量"; if(wasPlayingBeforeVoice) resumeMusic()
            }
            raw.contains("下一首") || raw.contains("切歌") || raw.contains("下一曲") || raw.contains("换一首") -> {
                voiceFeedback = "切换到下一首"; nextMusic()
            }
            raw.contains("上一首") || raw.contains("上一曲") -> {
                voiceFeedback = "回到上一首"; prevMusic()
            }
            raw.contains("暂停") || raw.contains("别放了") || raw.contains("停一下") || raw.contains("停止") || raw == "停" -> {
                voiceFeedback = "已为你暂停"; pauseMusic()
            }
            raw.contains("继续") || raw.contains("接着放") || raw.contains("接着播") || raw.contains("开始播放") -> {
                voiceFeedback = "继续播放"; resumeMusic()
            }
            raw.contains("加入") || raw.contains("添加") -> {
                val keyword = clean.replace("加入", "").replace("添加", "").replace("列表", "").replace("队列", "").trim()
                val songs = findSongsByTitleRobust(keyword)
                if (songs.isNotEmpty()) {
                    appendSongToVoiceQueue(songs.first())
                    voiceFeedback = "已加入语音队列: ${songs.first().title}"
                } else {
                    voiceFeedback = "未找到歌曲: $keyword"
                    if(wasPlayingBeforeVoice) { viewModelScope.launch { delay(1500); resumeMusic() } }
                }
            }
            matchedArtist != null -> {
                val artistSongs = songList.filter { ArtistAliasEngine.isArtistMatch(matchedArtist, it.artist) }
                var songSpecificKeyword = clean
                for (alias in ArtistAliasEngine.getAliases(matchedArtist)) {
                    songSpecificKeyword = songSpecificKeyword.replace(alias, "")
                }
                songSpecificKeyword = songSpecificKeyword
                    .replace("的歌", "")
                    .replace("歌曲", "")
                    .replace("单曲循环", "")
                    .replace("单曲", "")
                    .replace("随机", "")
                    .replace("顺序", "")
                    .replace("播放", "")
                    .replace("的", "")
                    .trim()

                if (songSpecificKeyword.isNotBlank() && songSpecificKeyword.length >= 1) {
                    val specificMatches = artistSongs.filter { s ->
                        s.title.lowercase().contains(songSpecificKeyword) ||
                                levenshteinDistance(songSpecificKeyword, s.title.lowercase()) <= maxOf(1, songSpecificKeyword.length / 3)
                    }
                    if (specificMatches.isNotEmpty()) {
                        if (specificMatches.size == 1) {
                            val targetSong = specificMatches.first()
                            val targetMode = if (isSingleLoopIntent) PlayMode.REPEAT_ONE else if (isShuffleIntent) PlayMode.SHUFFLE else PlayMode.SEQUENCE
                            setVoiceQueueAndPlay(artistSongs, targetSong, targetMode)
                            voiceFeedback = "正在${if (isSingleLoopIntent) "单曲循环" else "播放"} ${matchedArtist} 的 《${targetSong.title}》"
                        } else {
                            voiceFeedback = "找到 ${matchedArtist} 的多首同名歌曲，请选择"
                            val sortedMatches = specificMatches.sortedBy { abs(it.title.length - songSpecificKeyword.length) }.take(5)
                            presentSongSelection(sortedMatches) { target ->
                                val targetMode = if (isSingleLoopIntent) PlayMode.REPEAT_ONE else if (isShuffleIntent) PlayMode.SHUFFLE else PlayMode.SEQUENCE
                                setVoiceQueueAndPlay(artistSongs, target, targetMode)
                            }
                        }
                        return
                    }
                }

                if (artistSongs.isNotEmpty()) {
                    val targetMode = if (isSingleLoopIntent) PlayMode.REPEAT_ONE else if (isShuffleIntent) PlayMode.SHUFFLE else PlayMode.SEQUENCE
                    val modeText = if (isSingleLoopIntent) "单曲循环" else if (isShuffleIntent) "随机播放" else "顺序播放"
                    setVoiceQueueAndPlay(artistSongs, null, targetMode)
                    voiceFeedback = "找到 ${artistSongs.size} 首 ${matchedArtist} 的歌，正在${modeText}"
                } else {
                    voiceFeedback = "曲库中没有找到 ${matchedArtist} 的歌曲"
                    if(wasPlayingBeforeVoice) { viewModelScope.launch { delay(1500); resumeMusic() } }
                }
            }
            raw.contains("的歌") || raw.contains("歌手") -> {
                val potentialArtist = clean.substringBefore("的歌").substringAfter("歌手").trim()
                val songs = findSongsByArtistRobust(potentialArtist)
                if (songs.isNotEmpty()) {
                    val realArtistName = songs.first().artist
                    val targetMode = if (isSingleLoopIntent) PlayMode.REPEAT_ONE else if (isShuffleIntent) PlayMode.SHUFFLE else PlayMode.SEQUENCE
                    val modeText = if (isSingleLoopIntent) "单曲循环" else if (isShuffleIntent) "随机播放" else "顺序播放"
                    setVoiceQueueAndPlay(songs, null, targetMode)
                    voiceFeedback = "找到 ${songs.size} 首 ${realArtistName} 的歌，正在${modeText}"
                } else {
                    voiceFeedback = "没找到关于 $potentialArtist 的歌曲"
                    if(wasPlayingBeforeVoice) { viewModelScope.launch { delay(1500); resumeMusic() } }
                }
            }
            else -> {
                val targets = findDuplicateSongMatches(clean)
                if (targets.isEmpty()) {
                    val fallbackArtistSongs = findSongsByArtistRobust(clean)
                    if (fallbackArtistSongs.isNotEmpty()) {
                        val realArtistName = fallbackArtistSongs.first().artist
                        setVoiceQueueAndPlay(fallbackArtistSongs, null, if (isShuffleIntent) PlayMode.SHUFFLE else PlayMode.SEQUENCE)
                        voiceFeedback = "找到 ${fallbackArtistSongs.size} 首 ${realArtistName} 的歌，开始播放"
                    } else {
                        voiceFeedback = "曲库没找到: $clean"
                        if(wasPlayingBeforeVoice) { viewModelScope.launch { delay(1500); resumeMusic() } }
                    }
                } else if (targets.size == 1) {
                    val target = targets.first()
                    val targetMode = if (isSingleLoopIntent) PlayMode.REPEAT_ONE else null
                    voiceFeedback = "即将播放: ${target.title}"
                    if (targetMode != null) switchPlayMode(targetMode)

                    val activeList = getFilteredAllSongs()
                    if (activeList.any { it.id == target.id }) {
                        playSong(target, activeList, "全部歌曲")
                        requestedTab = "全部歌曲"
                    } else {
                        setVoiceQueueAndPlay(listOf(target), target, targetMode ?: PlayMode.SEQUENCE)
                    }
                } else {
                    voiceFeedback = "找到多首同名歌曲，请选择"
                    presentSongSelection(targets) { target ->
                        val targetMode = if (isSingleLoopIntent) PlayMode.REPEAT_ONE else null
                        if (targetMode != null) switchPlayMode(targetMode)

                        val activeList = getFilteredAllSongs()
                        if (activeList.any { it.id == target.id }) {
                            playSong(target, activeList, "全部歌曲")
                            requestedTab = "全部歌曲"
                        } else {
                            setVoiceQueueAndPlay(listOf(target), target, targetMode ?: PlayMode.SEQUENCE)
                        }
                    }
                }
            }
        }
        wasPlayingBeforeVoice = false
    }

    private fun adjustVol(up: Boolean) {
        val am = context.getSystemService(Context.AUDIO_SERVICE) as AudioManager
        am.adjustStreamVolume(AudioManager.STREAM_MUSIC, if (up) AudioManager.ADJUST_RAISE else AudioManager.ADJUST_LOWER, AudioManager.FLAG_SHOW_UI)
    }

    fun switchPlayMode(mode: PlayMode) {
        playMode = mode
        when(mode) {
            PlayMode.SEQUENCE -> { exoPlayer?.shuffleModeEnabled = false; exoPlayer?.repeatMode = Player.REPEAT_MODE_ALL }
            PlayMode.SHUFFLE -> { exoPlayer?.shuffleModeEnabled = true; exoPlayer?.repeatMode = Player.REPEAT_MODE_ALL }
            PlayMode.REPEAT_ONE -> { exoPlayer?.shuffleModeEnabled = false; exoPlayer?.repeatMode = Player.REPEAT_MODE_ONE }
        }
        updateNextSong()
    }

    private fun loadLyrics(path: String) {
        lrcJob?.cancel()
        currentLyrics = emptyList()
        lrcJob = viewModelScope.launch(Dispatchers.IO) {
            try {
                val audioFile = File(path)
                val customLrc = File(context.filesDir, "lyrics_${audioFile.nameWithoutExtension}.lrc")
                val localLrc = File(audioFile.parentFile, "${audioFile.nameWithoutExtension}.lrc")

                var raw = ""
                if (customLrc.exists()) raw = customLrc.readText()
                else if (localLrc.exists()) raw = localLrc.readText()
                else raw = AudioFileIO.read(audioFile).tag?.getFirst(FieldKey.LYRICS) ?: ""

                withContext(Dispatchers.Main) { rawLyricsText = raw }

                val timeRegex = "\\[(\\d{2}):(\\d{2})\\.(\\d{2,3})](.*)".toRegex()
                val rows = mutableListOf<LrcRow>()
                val introLines = mutableListOf<String>()
                var hasSeenTimedLine = false

                raw.split("\n").forEach { rawLine ->
                    val line = rawLine.trim()
                    if (line.isBlank()) return@forEach
                    val match = timeRegex.find(line)
                    if (match != null) {
                        hasSeenTimedLine = true
                        val ms = if (match.groupValues[3].length == 2) match.groupValues[3].toLong() * 10 else match.groupValues[3].toLong()
                        val timeInMs = match.groupValues[1].toLong() * 60000 + match.groupValues[2].toLong() * 1000 + ms
                        val text = match.groupValues[4].trim()
                        if (text.isNotBlank()) rows.add(LrcRow(timeInMs, text))
                    } else if (!hasSeenTimedLine) {
                        introLines.add(line)
                    }
                }

                val timedRows = rows.sortedBy { it.timeInMs }.toMutableList()
                val mergedRows = mutableListOf<LrcRow>()

                for (row in timedRows) {
                    val last = mergedRows.lastOrNull()
                    val isRowRoleInfo = row.text.startsWith("作词") || row.text.startsWith("作曲") || row.text.startsWith("编曲") || row.text.contains(":") || row.text.contains("：")

                    if (last != null && abs(last.timeInMs - row.timeInMs) <= 10) {
                        val isLastRoleInfo = last.text.startsWith("作词") || last.text.startsWith("作曲") || last.text.contains("：")
                        if (!isRowRoleInfo && !isLastRoleInfo) {
                            mergedRows[mergedRows.lastIndex] = last.copy(text = last.text + "\n" + row.text)
                        } else {
                            mergedRows.add(row)
                        }
                    } else {
                        mergedRows.add(row)
                    }
                }

                if (introLines.isNotEmpty()) {
                    val step = if (mergedRows.isNotEmpty() && mergedRows.first().timeInMs > 0) mergedRows.first().timeInMs / (introLines.size + 1) else 1800L
                    mergedRows.addAll(0, introLines.mapIndexed { index: Int, line: String -> LrcRow(step * (index + 1), line) })
                }

                if (mergedRows.isEmpty()) mergedRows.add(LrcRow(0, "纯音乐，请欣赏"))
                mergedRows.sortBy { it.timeInMs }
                withContext(Dispatchers.Main) { currentLyrics = mergedRows }
            } catch (e: Exception) {
                withContext(Dispatchers.Main) { currentLyrics = listOf(LrcRow(0, "暂无歌词")); rawLyricsText = "" }
            }
        }
    }

    fun saveCustomLyrics(song: Song?, text: String) {
        if (song == null) return
        try {
            val file = File(context.filesDir, "lyrics_${File(song.dataPath).nameWithoutExtension}.lrc")
            file.writeText(text)
            loadLyrics(song.dataPath)
            voiceFeedback = "歌词已更新"
        } catch (e: Exception) {
            voiceFeedback = "歌词保存失败"
        }
    }

    fun checkAndScan() { if (songList.isEmpty()) scan() }

    fun scan() {
        viewModelScope.launch(Dispatchers.IO) {
            withContext(Dispatchers.Main) { isScanning = true }
            val list = mutableListOf<Song>()
            val projection = arrayOf(MediaStore.Audio.Media._ID, MediaStore.Audio.Media.TITLE, MediaStore.Audio.Media.ARTIST, MediaStore.Audio.Media.ALBUM_ID, MediaStore.Audio.Media.DATA, MediaStore.Audio.Media.DURATION)
            val selection = "${MediaStore.Audio.Media.IS_MUSIC} != 0"
            val cursor = context.contentResolver.query(MediaStore.Audio.Media.EXTERNAL_CONTENT_URI, projection, selection, null, null)

            cursor?.use { c ->
                val idCol = c.getColumnIndexOrThrow(MediaStore.Audio.Media._ID)
                val titleCol = c.getColumnIndexOrThrow(MediaStore.Audio.Media.TITLE)
                val artistCol = c.getColumnIndexOrThrow(MediaStore.Audio.Media.ARTIST)
                val albumIdCol = c.getColumnIndexOrThrow(MediaStore.Audio.Media.ALBUM_ID)
                val dataCol = c.getColumnIndexOrThrow(MediaStore.Audio.Media.DATA)
                val durCol = c.getColumnIndexOrThrow(MediaStore.Audio.Media.DURATION)

                while (c.moveToNext()) {
                    val path = c.getString(dataCol) ?: continue
                    list.add(Song(
                        id = c.getLong(idCol), title = c.getString(titleCol) ?: "未知", artist = c.getString(artistCol) ?: "未知",
                        uri = ContentUris.withAppendedId(MediaStore.Audio.Media.EXTERNAL_CONTENT_URI, c.getLong(idCol)),
                        albumArtUri = ContentUris.withAppendedId(Uri.parse("content://media/external/audio/albumart"), c.getLong(albumIdCol)),
                        dataPath = path, duration = c.getLong(durCol)
                    ))
                }
            }

            val lastPosVal = prefs.getLong("lastPos", 0L)
            var initialTargetSong: Song? = null
            if (autoResumePlay && lastSongId != -1L) {
                initialTargetSong = list.find { it.id == lastSongId }
            }
            if (initialTargetSong == null && list.isNotEmpty()) {
                initialTargetSong = list.first()
            }

            withContext(Dispatchers.Main) {
                songList = list
                if (initialTargetSong != null) {
                    currentSong = initialTargetSong
                    exoPlayer?.setMediaItem(MediaItem.fromUri(initialTargetSong.uri))
                    exoPlayer?.seekTo(0, lastPosVal)
                    exoPlayer?.prepare()
                    exoPlayer?.play()
                    isPlaying = true
                    loadLyrics(initialTargetSong.dataPath)
                }
            }

            val loadedPlaylists = readPlaylistsSync(list)
            val favPlaylist = loadedPlaylists.find { it.name == FAVORITE_PLAYLIST_NAME }

            withContext(Dispatchers.Main) {
                playlists = loadedPlaylists
                favoriteSongIds.clear()
                favPlaylist?.songs?.forEach { favoriteSongIds[it.id] = true }

                val lastTab = prefs.getString("lastPlaylistTab", "全部歌曲") ?: "全部歌曲"
                var targetSongs = if (lastTab == "全部歌曲") getFilteredAllSongs() else playlists.find { it.name == lastTab }?.songs ?: emptyList()
                if (targetSongs.isEmpty()) targetSongs = getFilteredAllSongs()

                currentQueue = targetSongs
                exoPlayer?.setMediaItems(targetSongs.map { MediaItem.fromUri(it.uri) })
                val idx = if (initialTargetSong != null) targetSongs.indexOfFirst { it.id == initialTargetSong.id }.coerceAtLeast(0) else 0
                exoPlayer?.seekTo(idx, exoPlayer?.currentPosition ?: lastPosVal)
                requestedTab = lastTab
                updateNextSong()
                isScanning = false
            }
        }
    }

    override fun onCleared() {
        voiceManager?.release()
        mediaSession?.release()
        exoPlayer?.release()
        try { dynamicsProcessing?.release(); dynamicsProcessing = null } catch (_: Exception) {}
        try {
            equalizer?.release(); equalizer = null
            bassBoost?.release(); bassBoost = null
            presetReverb?.release(); presetReverb = null
            virtualizer?.release(); virtualizer = null
        } catch (_: Exception) {}
        super.onCleared()
    }
}

// ==========================================
// 5. 界面与渲染引擎
// ==========================================
@Composable
fun KeepScreenOnEffect(keep: Boolean, isPlaying: Boolean) {
    val context = LocalContext.current
    val activity = context as? Activity ?: return
    val window = activity.window
    DisposableEffect(keep, isPlaying) {
        if (keep && isPlaying) window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        else window.clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        onDispose { window.clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON) }
    }
}

@Composable
fun DynamicFluidBackground(albumArtUri: Uri?, lrcAlpha: Float, isDark: Boolean) {
    val safeAlpha = lrcAlpha.coerceIn(0f, 1f)
    val context = LocalContext.current

    Box(Modifier.fillMaxSize()) {
        AsyncImage(
            model = ImageRequest.Builder(context)
                .data(albumArtUri)
                .size(40)
                .crossfade(600)
                .build(),
            contentDescription = null,
            placeholder = rememberVectorPainter(Icons.Rounded.MusicNote),
            error = rememberVectorPainter(Icons.Rounded.MusicNote),
            fallback = rememberVectorPainter(Icons.Rounded.MusicNote),
            modifier = Modifier
                .fillMaxSize()
                .blur(16.dp, edgeTreatment = BlurredEdgeTreatment.Unbounded),
            contentScale = ContentScale.Crop
        )
        Box(
            modifier = Modifier
                .fillMaxSize()
                .background(
                    if (isDark) Color.Black.copy(alpha = safeAlpha.coerceAtLeast(0.5f))
                    else Color.White.copy(alpha = safeAlpha.coerceAtLeast(0.5f))
                )
        )
    }
}

@Composable
fun CompactDialogAction(text: String, icon: ImageVector, textMain: Color, onClick: () -> Unit) {
    Row(
        modifier = Modifier.fillMaxWidth().height(44.dp).clip(RoundedCornerShape(10.dp)).clickable { onClick() }.padding(horizontal = 8.dp),
        verticalAlignment = Alignment.CenterVertically
    ) {
        Icon(icon, contentDescription = null, tint = textMain, modifier = Modifier.size(22.dp)); Spacer(Modifier.width(10.dp))
        Text(text, color = textMain, fontSize = 14.sp, maxLines = 1, overflow = TextOverflow.Ellipsis)
    }
}

@Composable
fun PlaylistSongManageDialog(song: Song?, playlist: CustomPlaylist?, vm: MusicViewModel, onDismiss: () -> Unit, panelColor: Color, textMain: Color, textSub: Color) {
    if (song == null || playlist == null) return
    AlertDialog(
        onDismissRequest = onDismiss, modifier = Modifier.widthIn(max = 340.dp).padding(12.dp),
        title = { Column { Text("管理歌曲", color = textMain, fontSize = 18.sp, fontWeight = FontWeight.Bold); Text(song.title, color = textSub, fontSize = 12.sp, maxLines = 1, overflow = TextOverflow.Ellipsis) } },
        text = {
            Column {
                CompactDialogAction(text = "播放这首", icon = Icons.Rounded.PlayArrow, textMain = textMain) { vm.playSong(song, playlist.songs, playlist.name); onDismiss() }
                CompactDialogAction(text = "上移", icon = Icons.Rounded.KeyboardArrowUp, textMain = textMain) { vm.moveSongInPlaylist(playlist, song, -1); onDismiss() }
                CompactDialogAction(text = "下移", icon = Icons.Rounded.KeyboardArrowDown, textMain = textMain) { vm.moveSongInPlaylist(playlist, song, 1); onDismiss() }
                Spacer(Modifier.height(6.dp))
                CompactDialogAction(text = "从该播放列表删除", icon = Icons.Rounded.DeleteOutline, textMain = Color(0xFFFF5252)) { vm.removeSongFromM3uPlaylist(playlist, song); onDismiss() }
            }
        },
        confirmButton = { TextButton(onClick = onDismiss) { Text("关闭", color = textMain, fontSize = 14.sp) } },
        containerColor = panelColor, shape = RoundedCornerShape(22.dp)
    )
}

@Composable
fun LyricEngineView(lyrics: List<LrcRow>, vm: MusicViewModel, fontSize: Float, spacing: Float, textColor: Color = Color.White) {
    var localPos by remember { mutableStateOf(0L) }
    val context = LocalContext.current

    LaunchedEffect(vm.currentSong) {
        while(isActive) {
            localPos = vm.getCurrentPosition(); delay(80)
        }
    }

    val scrollState = rememberLazyListState()
    val currentIndex = lyrics.indexOfLast { row: LrcRow -> row.timeInMs <= localPos + 100 }.coerceAtLeast(0)

    val isFinished = lyrics.isNotEmpty() && currentIndex == lyrics.lastIndex && localPos > (lyrics.last().timeInMs + 5000L)
    val overallAlpha by animateFloatAsState(
        targetValue = if (isFinished) 0f else 1f,
        animationSpec = tween(1200, easing = CubicBezierEasing(0.25f, 0.1f, 0.25f, 1f)),
        label = "lrc_exit_fade"
    )

    val isLightText = (textColor.red + textColor.green + textColor.blue) > 1.2f
    val activeShadow = if (isLightText) Shadow(color = Color.Black.copy(alpha = 0.8f), offset = Offset(0f, 2f), blurRadius = 6f) else null

    BoxWithConstraints(modifier = Modifier
        .fillMaxSize()
        .graphicsLayer { compositingStrategy = CompositingStrategy.Offscreen }
        .drawWithContent {
            drawContent()
            drawRect(
                brush = Brush.verticalGradient(0f to Color.Transparent, 0.32f to Color.Black, 0.68f to Color.Black, 1f to Color.Transparent),
                blendMode = BlendMode.DstIn
            )
        }
    ) {
        val verticalPadding = max(0.dp, maxHeight / 2 - (fontSize.dp / 2))
        LaunchedEffect(currentIndex) {
            if (lyrics.isNotEmpty() && currentIndex in lyrics.indices && !scrollState.isScrollInProgress) {
                scrollState.animateScrollToItem(index = currentIndex, scrollOffset = 0)
            }
        }

        val currentFontFamily = when(vm.lrcFont) {
            1 -> FontFamily.Serif
            2 -> FontFamily.Monospace
            3 -> FontFamily.Cursive
            4 -> FontFamily.SansSerif
            5 -> getCustomFontFamily(context, "luolicat")
            6 -> getCustomFontFamily(context, "alibaba")
            7 -> getCustomFontFamily(context, "fangzhengxingkai")
            8 -> getCustomFontFamily(context, "debiaogangbixingshu")
            9 -> getCustomFontFamily(context, "caomeiti")
            10 -> getCustomFontFamily(context, "jianzhi")
            else -> FontFamily.Default
        }

        LazyColumn(
            state = scrollState,
            modifier = Modifier
                .fillMaxSize()
                .graphicsLayer { alpha = overallAlpha },
            contentPadding = PaddingValues(vertical = verticalPadding),
            horizontalAlignment = Alignment.CenterHorizontally
        ) {
            itemsIndexed(items = lyrics, key = { index: Int, row: LrcRow -> "${row.timeInMs}_$index" }) { index: Int, row: LrcRow ->
                val isSelected = index == currentIndex
                val softEasing = CubicBezierEasing(0.18f, 0.85f, 0.18f, 1f)

                val animatedColor by animateColorAsState(
                    targetValue = if (isSelected) textColor else textColor.copy(alpha = 0.35f),
                    animationSpec = tween(500, easing = softEasing),
                    label = "lrc_text_color"
                )

                val scale by animateFloatAsState(
                    targetValue = if (isSelected) 1.12f else 0.85f,
                    animationSpec = tween(600, easing = softEasing),
                    label = "scale"
                )
                val offsetY by animateFloatAsState(
                    targetValue = if (isSelected) 0f else 10f,
                    animationSpec = tween(600, easing = softEasing),
                    label = "offsetY"
                )

                val currentShadow = if (isSelected) activeShadow else null
                val lines = row.text.split("\n")

                Column(
                    modifier = Modifier
                        .fillMaxWidth(0.92f)
                        .padding(vertical = (spacing / 2).dp)
                        .graphicsLayer {
                            this.scaleX = scale
                            this.scaleY = scale
                            this.translationY = offsetY
                        },
                    horizontalAlignment = Alignment.CenterHorizontally
                ) {
                    val mainLine = lines[0]
                    val mainLetterSpacing = if (mainLine.length <= 4) (-0.5f).sp else 0.sp
                    Text(
                        text = mainLine,
                        color = animatedColor,
                        fontSize = fontSize.sp,
                        fontFamily = currentFontFamily,
                        fontWeight = FontWeight.Bold,
                        textAlign = TextAlign.Center,
                        style = TextStyle(
                            lineHeight = (fontSize * 1.35f).sp,
                            letterSpacing = mainLetterSpacing,
                            shadow = currentShadow
                        ),
                        softWrap = true
                    )

                    if (lines.size > 1) {
                        for (i in 1 until lines.size) {
                            Spacer(Modifier.height(4.dp))
                            val subLine = lines[i]
                            val subLetterSpacing = if (subLine.length <= 3) (-0.4f).sp else 0.sp
                            Text(
                                text = subLine,
                                color = animatedColor.copy(alpha = if (isSelected) 0.75f else 0.35f),
                                fontSize = (fontSize * 0.72f).coerceAtLeast(12f).sp,
                                fontFamily = currentFontFamily,
                                fontWeight = FontWeight.Medium,
                                textAlign = TextAlign.Center,
                                style = TextStyle(
                                    lineHeight = (fontSize * 1.0f).sp,
                                    letterSpacing = subLetterSpacing,
                                    shadow = currentShadow
                                ),
                                softWrap = true
                            )
                        }
                    }
                }
            }
        }
    }
}

@Composable
fun DuplicateSongChoiceDialog(
    songs: List<Song>,
    countdown: Int,
    onSelect: (Song) -> Unit,
    panelColor: Color,
    textMain: Color,
    textSub: Color
) {
    AlertDialog(
        onDismissRequest = {},
        modifier = Modifier
            .widthIn(max = 380.dp)
            .padding(16.dp)
            .border(1.dp, textMain.copy(0.12f), RoundedCornerShape(24.dp)),
        title = {
            Row(
                modifier = Modifier.fillMaxWidth(),
                horizontalArrangement = Arrangement.SpaceBetween,
                verticalAlignment = Alignment.CenterVertically
            ) {
                Text(
                    text = "同名歌曲选择",
                    color = textMain,
                    fontSize = 18.sp,
                    fontWeight = FontWeight.Bold
                )
                Box(
                    modifier = Modifier
                        .size(32.dp)
                        .clip(CircleShape)
                        .background(Color(0xFFFF5252).copy(0.12f)),
                    contentAlignment = Alignment.Center
                ) {
                    Text(
                        text = countdown.toString(),
                        color = Color(0xFFFF5252),
                        fontSize = 14.sp,
                        fontWeight = FontWeight.Black
                    )
                }
            }
        },
        text = {
            Column(
                modifier = Modifier.fillMaxWidth(),
                verticalArrangement = Arrangement.spacedBy(10.dp)
            ) {
                Text(
                    text = "系统将在倒计时结束后默认播放第一首歌曲。",
                    color = textSub,
                    fontSize = 12.sp,
                    modifier = Modifier.padding(bottom = 6.dp)
                )
                songs.forEachIndexed { index, song ->
                    val isBestMatch = index == 0
                    Row(
                        modifier = Modifier
                            .fillMaxWidth()
                            .height(64.dp)
                            .clip(RoundedCornerShape(16.dp))
                            .background(
                                if (isBestMatch) textMain.copy(0.08f) else Color.Transparent
                            )
                            .border(
                                width = 1.dp,
                                color = if (isBestMatch) Color(0xFF7C4DFF).copy(0.25f) else textMain.copy(0.04f),
                                shape = RoundedCornerShape(16.dp)
                            )
                            .clickable { onSelect(song) }
                            .padding(horizontal = 14.dp),
                        verticalAlignment = Alignment.CenterVertically
                    ) {
                        Column(modifier = Modifier.weight(1f)) {
                            Text(
                                text = song.title,
                                color = textMain,
                                fontSize = 15.sp,
                                fontWeight = FontWeight.Bold,
                                maxLines = 1,
                                overflow = TextOverflow.Ellipsis
                            )
                            Spacer(Modifier.height(2.dp))
                            Text(
                                text = song.artist,
                                color = textSub,
                                fontSize = 12.sp,
                                maxLines = 1,
                                overflow = TextOverflow.Ellipsis
                            )
                        }
                        if (isBestMatch) {
                            Box(
                                modifier = Modifier
                                    .clip(RoundedCornerShape(6.dp))
                                    .background(Color(0xFF7C4DFF).copy(0.12f))
                                    .padding(horizontal = 6.dp, vertical = 2.dp)
                            ) {
                                Text(
                                    text = "推荐",
                                    color = Color(0xFF7C4DFF),
                                    fontSize = 10.sp,
                                    fontWeight = FontWeight.Bold
                                )
                            }
                        }
                    }
                }
            }
        },
        confirmButton = {},
        containerColor = panelColor.copy(0.96f),
        shape = RoundedCornerShape(24.dp)
    )
}

@Composable
fun AppRouter(vm: MusicViewModel) {
    val conf = LocalConfiguration.current
    val systemDark = isSystemInDarkTheme()
    val isDark = when (vm.themeMode) { 1 -> false; 2 -> true; else -> systemDark }

    val textMain = if (isDark) Color(0xFFE2E4E9) else Color(0xFF1C1D21)
    val textSub = if (isDark) Color(0xFF8E95A3) else Color(0xFF6B7280)
    val panelColor = if (isDark) Color(0xFF0D0E12).copy(alpha = 0.90f) else Color(0xFFF3F4F6).copy(alpha = 0.94f)

    if (conf.orientation == Configuration.ORIENTATION_PORTRAIT) DashboardPortrait(vm, panelColor, textMain, textSub, isDark)
    else DashboardLandscape(vm, panelColor, textMain, textSub, isDark)

    if (vm.duplicateSongsToResolve.isNotEmpty()) {
        DuplicateSongChoiceDialog(
            songs = vm.duplicateSongsToResolve,
            countdown = vm.duplicateSelectionCountdown,
            onSelect = { song -> vm.selectDuplicateSong(song) },
            panelColor = panelColor,
            textMain = textMain,
            textSub = textSub
        )
    }
}

@Composable
fun VoiceFeedbackText(feedback: String, vState: VoiceState) {
    if (vState == VoiceState.IDLE || feedback.isBlank()) return
    val color = when (vState) {
        VoiceState.RECORDING -> Color(0xFFFF5252)
        VoiceState.RECOGNIZING -> Color(0xFF4CAF50)
        else -> Color.White.copy(alpha = 0.75f)
    }
    Text(
        text = feedback,
        color = color,
        fontSize = 14.sp,
        fontWeight = FontWeight.Medium,
        textAlign = TextAlign.Center,
        maxLines = 1,
        overflow = TextOverflow.Ellipsis,
        modifier = Modifier
            .fillMaxWidth()
            .padding(horizontal = 16.dp, vertical = 4.dp)
    )
}

@Composable
fun PlayerSlider(vm: MusicViewModel, textColor: Color) {
    val exoDur = vm.exoPlayer?.duration ?: 0L
    val rangeMax = if (exoDur > 0) exoDur.toFloat() else (vm.currentSong?.duration?.toFloat() ?: 0f)
    val safeMax = if (rangeMax > 0f) rangeMax else 1f

    var localPos by remember(vm.currentSong) { mutableStateOf(0f) }
    var isDragging by remember { mutableStateOf(false) }

    LaunchedEffect(isDragging, vm.currentSong) {
        while(isActive && !isDragging) {
            val pos = vm.getCurrentPosition().toFloat()
            if (pos >= 0f) localPos = pos
            delay(250)
        }
    }

    Column(modifier = Modifier.fillMaxWidth().padding(vertical = 12.dp)) {
        BoxWithConstraints(
            modifier = Modifier
                .fillMaxWidth()
                .height(32.dp)
                .pointerInput(safeMax) {
                    detectTapGestures { offset ->
                        val ratio = (offset.x / size.width).coerceIn(0f, 1f)
                        val newPos = ratio * safeMax
                        localPos = newPos
                        vm.exoPlayer?.seekTo(newPos.toLong())
                    }
                }
                .pointerInput(safeMax) {
                    detectDragGestures(
                        onDragStart = { isDragging = true },
                        onDragEnd = {
                            vm.exoPlayer?.seekTo(localPos.toLong())
                            isDragging = false
                        },
                        onDragCancel = { isDragging = false },
                        onDrag = { change, dragAmount ->
                            change.consume()
                            val newX = change.position.x.coerceIn(0f, size.width.toFloat())
                            val ratio = newX / size.width
                            localPos = ratio * safeMax
                        }
                    )
                },
            contentAlignment = Alignment.CenterStart
        ) {
            val fraction = (localPos / safeMax).coerceIn(0f, 1f)
            Box(modifier = Modifier.fillMaxWidth().height(4.dp).clip(CircleShape).background(textColor.copy(alpha = 0.15f)))
            Box(modifier = Modifier.fillMaxWidth(fraction).height(4.dp).clip(CircleShape).background(textColor))
        }
        Row(modifier = Modifier.fillMaxWidth().padding(top = 4.dp), horizontalArrangement = Arrangement.SpaceBetween) {
            Text(text = formatTime(localPos.toLong()), color = textColor.copy(alpha = 0.5f), fontSize = 11.sp, fontWeight = FontWeight.Medium)
            Text(text = formatTime(rangeMax.toLong()), color = textColor.copy(alpha = 0.5f), fontSize = 11.sp, fontWeight = FontWeight.Medium)
        }
    }
}

private fun formatTime(ms: Long): String { val totalSec = ms / 1000; val min = totalSec / 60; val sec = totalSec % 60; return "%02d:%02d".format(min, sec) }

@OptIn(ExperimentalFoundationApi::class)
@Composable
fun RoundControlButton(
    onClick: () -> Unit,
    modifier: Modifier = Modifier,
    onLongClick: (() -> Unit)? = null,
    content: @Composable BoxScope.() -> Unit
) {
    val interactionSource = remember { MutableInteractionSource() }
    val isPressed by interactionSource.collectIsPressedAsState()
    val scale by animateFloatAsState(
        targetValue = if (isPressed) 0.9f else 1f,
        animationSpec = spring(dampingRatio = Spring.DampingRatioMediumBouncy),
        label = "button_press"
    )

    val clickModifier = if (onLongClick != null) {
        Modifier.combinedClickable(interactionSource = interactionSource, indication = null, onClick = onClick, onLongClick = onLongClick)
    } else {
        Modifier.clickable(interactionSource = interactionSource, indication = null) { onClick() }
    }
    Box(
        modifier = modifier
            .size(52.dp)
            .clip(CircleShape)
            .graphicsLayer { scaleX = scale; scaleY = scale }
            .then(clickModifier),
        contentAlignment = Alignment.Center,
        content = content
    )
}

@Composable
fun SharedPlaybackControls(vm: MusicViewModel, textMain: Color, textSub: Color, panelColor: Color, isDark: Boolean, isListMode: Boolean, onTogglePlaylistMode: () -> Unit) {
    val vState = vm.voiceManager?.currentState ?: VoiceState.IDLE
    var showPlaylistMenu by remember { mutableStateOf(false) }
    var showCreateDialog by remember { mutableStateOf(false) }

    Column(Modifier.fillMaxWidth()) {
        PlayerSlider(vm = vm, textColor = textMain)
        VoiceFeedbackText(vm.voiceFeedback, vState)
        Spacer(Modifier.height(10.dp))

        Row(modifier = Modifier.fillMaxWidth().padding(top = 8.dp), verticalAlignment = Alignment.CenterVertically) {
            Box(
                modifier = Modifier
                    .size(80.dp)
                    .clip(CircleShape)
                    .background(Color.Transparent)
                    .voicePressHandler(
                        onPressStart = { vm.startPressTalk() },
                        onPressEnd = { vm.stopPressTalk() }
                    ),
                contentAlignment = Alignment.Center
            ) {
                Icon(
                    imageVector = if (vState == VoiceState.RECOGNIZING) Icons.Rounded.Autorenew else Icons.Rounded.Mic,
                    contentDescription = null,
                    tint = when (vState) {
                        VoiceState.RECORDING -> Color(0xFFFF5252)
                        VoiceState.RECOGNIZING -> Color(0xFF4CAF50)
                        else -> textMain
                    },
                    modifier = Modifier.size(36.dp)
                )
            }
            Spacer(Modifier.width(10.dp))

            Row(verticalAlignment = Alignment.CenterVertically, horizontalArrangement = Arrangement.spacedBy(16.dp)) {
                RoundControlButton(onClick = { vm.prevMusic() }, modifier = Modifier.size(60.dp)) { Icon(Icons.Rounded.SkipPrevious, null, tint = textMain, modifier = Modifier.size(36.dp)) }

                Box(
                    modifier = Modifier
                        .size(80.dp)
                        .clip(CircleShape)
                        .background(textMain)
                        .clickable { vm.togglePlayPause() },
                    contentAlignment = Alignment.Center
                ) { Icon(if (vm.isPlaying) Icons.Rounded.Pause else Icons.Rounded.PlayArrow, null, tint = if (isDark) Color.Black else Color.White, modifier = Modifier.size(44.dp)) }

                RoundControlButton(onClick = { vm.nextMusic() }, modifier = Modifier.size(60.dp)) { Icon(Icons.Rounded.SkipNext, null, tint = textMain, modifier = Modifier.size(36.dp)) }
            }
            Spacer(Modifier.weight(1f))
            Row(verticalAlignment = Alignment.CenterVertically, horizontalArrangement = Arrangement.spacedBy(8.dp)) {
                RoundControlButton(onClick = { vm.switchPlayMode(when (vm.playMode) { PlayMode.SHUFFLE -> PlayMode.SEQUENCE; PlayMode.SEQUENCE -> PlayMode.REPEAT_ONE; PlayMode.REPEAT_ONE -> PlayMode.SHUFFLE }) }) {
                    Icon(when (vm.playMode) { PlayMode.SHUFFLE -> Icons.Rounded.Shuffle; PlayMode.REPEAT_ONE -> Icons.Rounded.RepeatOne; PlayMode.SEQUENCE -> Icons.Rounded.Repeat }, null, tint = textMain, modifier = Modifier.size(24.dp))
                }

                val isFav = vm.isFavorite(vm.currentSong)
                val heartScale by animateFloatAsState(
                    targetValue = if (isFav) 1.28f else 1.0f,
                    animationSpec = spring(dampingRatio = Spring.DampingRatioMediumBouncy, stiffness = Spring.StiffnessMedium),
                    label = "heart_bounce"
                )
                RoundControlButton(onClick = { vm.currentSong?.let { vm.toggleFavorite(it) } }) {
                    Icon(
                        imageVector = if (isFav) Icons.Rounded.Favorite else Icons.Rounded.FavoriteBorder,
                        contentDescription = "收藏最爱",
                        tint = if (isFav) Color(0xFFFF5252) else textSub,
                        modifier = Modifier.size(26.dp).graphicsLayer { scaleX = heartScale; scaleY = heartScale }
                    )
                }

                Box(contentAlignment = Alignment.Center) {
                    RoundControlButton(onClick = { showPlaylistMenu = true }) {
                        Icon(imageVector = Icons.Rounded.PlaylistAdd, contentDescription = "管理播放列表", tint = textSub, modifier = Modifier.size(26.dp))
                    }

                    DropdownMenu(
                        expanded = showPlaylistMenu, onDismissRequest = { showPlaylistMenu = false },
                        modifier = Modifier.width(180.dp).background(panelColor, RoundedCornerShape(16.dp))
                    ) {
                        vm.playlists.filter { it.name != vm.FAVORITE_PLAYLIST_NAME }.forEach { targetPlaylist: CustomPlaylist ->
                            val inThis = targetPlaylist.songs.any { s: Song -> s.id == vm.currentSong?.id }
                            DropdownMenuItem(
                                text = { Text(targetPlaylist.name, color = textMain, fontSize = 14.sp, fontWeight = if(inThis) FontWeight.Bold else FontWeight.Normal) },
                                trailingIcon = { if(inThis) Icon(Icons.Rounded.Check, null, tint = Color(0xFFFF5252), modifier = Modifier.size(18.dp)) },
                                onClick = {
                                    vm.currentSong?.let { song ->
                                        if(inThis) vm.removeSongFromPlaylist(targetPlaylist, song)
                                        else vm.addSongToPlaylist(targetPlaylist, song)
                                    }
                                    showPlaylistMenu = false
                                }
                            )
                        }
                        HorizontalDivider(color = textMain.copy(0.1f), modifier = Modifier.padding(vertical = 4.dp))
                        DropdownMenuItem(
                            text = { Text("新建列表", color = textMain, fontSize = 14.sp) },
                            leadingIcon = { Icon(Icons.Rounded.Add, null, tint = textMain, modifier = Modifier.size(20.dp)) },
                            onClick = { showPlaylistMenu = false; showCreateDialog = true }
                        )
                    }
                }

                RoundControlButton(onClick = onTogglePlaylistMode) {
                    Icon(Icons.Rounded.QueueMusic, null, tint = if(isListMode) Color(0xFF7C4DFF) else textMain, modifier = Modifier.size(24.dp))
                }
            }
        }
    }

    if (showCreateDialog) {
        var name by remember { mutableStateOf("") }
        AlertDialog(
            onDismissRequest = { showCreateDialog = false }, modifier = Modifier.widthIn(max = 340.dp).padding(12.dp),
            title = { Text("新建播放列表", color = textMain, fontSize = 18.sp, fontWeight = FontWeight.Bold) },
            text = { OutlinedTextField(value = name, onValueChange = { name = it }, textStyle = TextStyle(color = textMain, fontSize = 14.sp), singleLine = true, placeholder = { Text("输入名称", color = textMain.copy(alpha = 0.45f)) }) },
            confirmButton = { TextButton(onClick = { if (name.isNotBlank()) vm.createPlaylist(name.trim()); showCreateDialog = false }) { Text("创建", color = textMain) } },
            dismissButton = { TextButton(onClick = { showCreateDialog = false }) { Text("取消", color = textMain.copy(alpha = 0.7f)) } }, containerColor = panelColor, shape = RoundedCornerShape(22.dp)
        )
    }
}

@OptIn(ExperimentalFoundationApi::class)
@Composable
fun PlaylistComponent(vm: MusicViewModel, textMain: Color, textSub: Color, isDark: Boolean, onOpenSettings: () -> Unit, modifier: Modifier) {
    var manageSong by remember { mutableStateOf<Song?>(null) }
    var managePlaylist by remember { mutableStateOf<CustomPlaylist?>(null) }
    val coroutineScope = rememberCoroutineScope()
    val keyboardController = LocalSoftwareKeyboardController.current

    val localPanelColor = if (isDark) Color(0xFF0D0E12) else Color(0xFFF3F4F6)
    var activeDragLetter by remember { mutableStateOf<Char?>(null) }
    var searchQuery by remember { mutableStateOf("") }

    PlaylistSongManageDialog(song = manageSong, playlist = managePlaylist, vm = vm, onDismiss = { manageSong = null; managePlaylist = null }, panelColor = if (isDark) Color.Black else Color.White, textMain = textMain, textSub = textSub)

    Column(modifier = modifier, verticalArrangement = Arrangement.SpaceBetween) {
        val tabs = remember(vm.playlists, vm.voiceQueue) {
            val base = listOf("全部歌曲")
            val withVoice = if (vm.voiceQueue.isNotEmpty()) base + "语音队列" else base
            withVoice + vm.playlists.map { it.name }
        }
        var selectedTab by remember { mutableStateOf(0) }
        LaunchedEffect(vm.requestedTab, tabs) {
            vm.requestedTab?.let {
                val idx = tabs.indexOf(it)
                if (idx != -1) selectedTab = idx
                vm.requestedTab = null
            }
        }

        Box(modifier = Modifier.fillMaxWidth().padding(bottom = 6.dp).clip(RoundedCornerShape(20.dp)).background(if (isDark) Color.Black.copy(0.24f) else Color.White.copy(0.34f))) {
            Row(modifier = Modifier.fillMaxWidth().padding(4.dp), verticalAlignment = Alignment.CenterVertically) {
                Row(modifier = Modifier.weight(1f)) {
                    tabs.forEachIndexed { index: Int, title: String ->
                        Box(
                            modifier = Modifier.weight(1f).height(36.dp).clip(RoundedCornerShape(12.dp)).background(if (selectedTab == index) { if (isDark) Color.White.copy(alpha = 0.16f) else Color.Black.copy(alpha = 0.08f) } else Color.Transparent).clickable { selectedTab = index; searchQuery = "" },
                            contentAlignment = Alignment.Center
                        ) { Text(text = title, color = if (selectedTab == index) textMain else textSub, fontSize = 14.sp, fontWeight = FontWeight.Bold, maxLines = 1, overflow = TextOverflow.Ellipsis) }
                    }
                }
                IconButton(onClick = onOpenSettings) { Icon(Icons.Rounded.Settings, null, tint = textMain) }
            }
        }

        Row(
            modifier = Modifier
                .fillMaxWidth()
                .height(36.dp)
                .clip(RoundedCornerShape(10.dp))
                .background(if (isDark) Color.Black.copy(0.2f) else Color.White.copy(0.3f))
                .border(1.dp, textMain.copy(0.08f), RoundedCornerShape(10.dp))
                .padding(horizontal = 10.dp),
            verticalAlignment = Alignment.CenterVertically
        ) {
            Icon(Icons.Rounded.Search, null, tint = textSub, modifier = Modifier.size(16.dp))
            Spacer(Modifier.width(8.dp))
            Box(modifier = Modifier.weight(1f), contentAlignment = Alignment.CenterStart) {
                if (searchQuery.isEmpty()) {
                    Text("在当前列表中查找...", color = textSub.copy(0.5f), fontSize = 12.sp)
                }
                BasicTextField(
                    value = searchQuery,
                    onValueChange = { searchQuery = it },
                    singleLine = true,
                    textStyle = TextStyle(color = textMain, fontSize = 13.sp),
                    keyboardOptions = KeyboardOptions(imeAction = ImeAction.Search),
                    keyboardActions = KeyboardActions(onSearch = { keyboardController?.hide() }),
                    modifier = Modifier.fillMaxWidth()
                )
            }
            if (searchQuery.isNotEmpty()) {
                Icon(
                    imageVector = Icons.Rounded.Close,
                    contentDescription = null,
                    tint = textSub,
                    modifier = Modifier.size(16.dp).clickable { searchQuery = "" }
                )
            }
        }

        Spacer(Modifier.height(6.dp))

        Box(modifier = Modifier.weight(1f).padding(bottom = 4.dp)) {
            val currentTabName = tabs.getOrNull(selectedTab) ?: "全部歌曲"
            val currentPlaylist = vm.playlists.find { playlist: CustomPlaylist -> playlist.name == currentTabName }

            val displaySongs = remember(currentTabName, vm.songList, vm.playlists, vm.excludePlaylistNames, vm.voiceQueue) {
                val raw = when (currentTabName) {
                    "全部歌曲" -> vm.getFilteredAllSongs()
                    "语音队列" -> vm.voiceQueue
                    else -> currentPlaylist?.songs ?: emptyList()
                }
                raw.sortedWith(
                    compareBy<Song> { song ->
                        val initial = getInitialLetter(song.title)
                        if (initial == '#') 'Z' + 1 else initial
                    }.thenBy { it.title.lowercase() }
                )
            }

            val filteredSongs = remember(displaySongs, searchQuery) {
                if (searchQuery.isBlank()) displaySongs
                else displaySongs.filter { it.title.contains(searchQuery, ignoreCase = true) || it.artist.contains(searchQuery, ignoreCase = true) }
            }

            val listState = rememberLazyListState()
            val currentIndex = filteredSongs.indexOfFirst { s: Song -> s.id == vm.currentSong?.id }

            LaunchedEffect(currentIndex, currentTabName) {
                if (currentIndex in filteredSongs.indices && !listState.isScrollInProgress) {
                    listState.animateScrollToItem(index = currentIndex, scrollOffset = 0)
                }
            }

            val alphabet = remember { ('A'..'Z').toList() + '#' }
            val firstIndices = remember(filteredSongs) {
                val map = mutableMapOf<Char, Int>()
                filteredSongs.forEachIndexed { index: Int, song: Song ->
                    val initial = getInitialLetter(song.title)
                    if (!map.containsKey(initial)) map[initial] = index
                }
                map
            }

            var indexBarHeight by remember { mutableStateOf(0f) }

            Box(modifier = Modifier.fillMaxSize()) {
                Row(
                    modifier = Modifier
                        .fillMaxSize()
                        .clip(RoundedCornerShape(20.dp))
                        .background(if (isDark) Color.Black.copy(0.34f) else Color.White.copy(0.46f))
                ) {
                    BoxWithConstraints(modifier = Modifier.weight(1f).fillMaxHeight()) {
                        val itemHeight = 54.dp
                        val availableHeight = maxHeight - 32.dp
                        val fitCount = (availableHeight / itemHeight).toInt().coerceAtLeast(1)
                        val exactHeight = itemHeight * fitCount

                        Box(modifier = Modifier.fillMaxSize(), contentAlignment = Alignment.Center) {
                            LazyColumn(
                                state = listState,
                                flingBehavior = rememberSnapFlingBehavior(lazyListState = listState),
                                modifier = Modifier.fillMaxWidth().height(exactHeight),
                                contentPadding = PaddingValues(0.dp)
                            ) {
                                itemsIndexed(items = filteredSongs, key = { index, song -> "${song.id}_$index" }) { index, s ->
                                    val isSelected = vm.currentSong?.id == s.id
                                    Row(
                                        modifier = Modifier.fillMaxWidth().height(54.dp).padding(horizontal = 8.dp, vertical = 2.dp)
                                            .clip(RoundedCornerShape(12.dp))
                                            .background(if (isSelected) textMain.copy(alpha = 0.15f) else Color.Transparent)
                                            .combinedClickable(
                                                onClick = {
                                                    keyboardController?.hide()
                                                    vm.playSong(s, filteredSongs, currentTabName)
                                                },
                                                onLongClick = { if (currentPlaylist != null) { manageSong = s; managePlaylist = currentPlaylist } }
                                            ).padding(horizontal = 12.dp),
                                        verticalAlignment = Alignment.CenterVertically
                                    ) {
                                        if (isSelected) { Box(Modifier.width(4.dp).height(18.dp).background(textMain, CircleShape)); Spacer(Modifier.width(8.dp)) }
                                        Column(Modifier.weight(1f).padding(end = 6.dp)) {
                                            Text(text = s.title, color = textMain, fontSize = 15.sp, fontWeight = if(isSelected) FontWeight.Bold else FontWeight.Medium, maxLines = 1, overflow = TextOverflow.Ellipsis)
                                            Text(text = s.artist, color = if(isSelected) textMain.copy(0.85f) else textSub, fontSize = 12.sp, maxLines = 1, overflow = TextOverflow.Ellipsis)
                                        }
                                        if(isSelected) Icon(Icons.Rounded.Equalizer, null, tint = textMain, modifier = Modifier.size(16.dp))
                                    }
                                }
                            }
                        }
                    }

                    Column(
                        modifier = Modifier
                            .fillMaxHeight()
                            .width(26.dp)
                            .background(if (isDark) Color.White.copy(0.02f) else Color.Black.copy(0.01f))
                            .padding(vertical = 16.dp)
                            .onGloballyPositioned { indexBarHeight = it.size.height.toFloat() }
                            .pointerInput(indexBarHeight, firstIndices) {
                                detectDragGestures(
                                    onDragStart = { offset ->
                                        if (indexBarHeight > 0f) {
                                            val idx = ((offset.y / indexBarHeight) * alphabet.size).toInt().coerceIn(0, alphabet.lastIndex)
                                            val letter = alphabet[idx]
                                            activeDragLetter = letter
                                            firstIndices[letter]?.let { target -> coroutineScope.launch { listState.scrollToItem(target) } }
                                        }
                                    },
                                    onDrag = { change, _ ->
                                        if (indexBarHeight > 0f) {
                                            val idx = ((change.position.y / indexBarHeight) * alphabet.size).toInt().coerceIn(0, alphabet.lastIndex)
                                            val letter = alphabet[idx]
                                            if (activeDragLetter != letter) {
                                                activeDragLetter = letter
                                                firstIndices[letter]?.let { target -> coroutineScope.launch { listState.scrollToItem(target) } }
                                            }
                                        }
                                    },
                                    onDragEnd = { activeDragLetter = null },
                                    onDragCancel = { activeDragLetter = null }
                                )
                            },
                        verticalArrangement = Arrangement.SpaceBetween,
                        horizontalAlignment = Alignment.CenterHorizontally
                    ) {
                        alphabet.forEach { char: Char ->
                            val hasTarget = firstIndices.containsKey(char)
                            Box(
                                modifier = Modifier
                                    .weight(1f)
                                    .fillMaxWidth()
                                    .clickable(enabled = hasTarget) {
                                        firstIndices[char]?.let { targetIndex -> coroutineScope.launch { listState.animateScrollToItem(targetIndex) } }
                                    },
                                contentAlignment = Alignment.Center
                            ) {
                                Text(
                                    text = char.toString(),
                                    color = if (hasTarget) textMain else textSub.copy(alpha = 0.20f),
                                    fontSize = 9.sp,
                                    fontWeight = if (hasTarget) FontWeight.Black else FontWeight.Normal
                                )
                            }
                        }
                    }
                }

                androidx.compose.animation.AnimatedVisibility(
                    visible = activeDragLetter != null,
                    enter = scaleIn(animationSpec = spring(dampingRatio = Spring.DampingRatioMediumBouncy, stiffness = Spring.StiffnessMedium)) + fadeIn(),
                    exit = scaleOut() + fadeOut(),
                    modifier = Modifier.align(Alignment.Center)
                ) {
                    Box(
                        modifier = Modifier
                            .size(80.dp)
                            .clip(CircleShape)
                            .background(textMain.copy(alpha = 0.9f))
                            .border(2.dp, Color.White.copy(0.2f), CircleShape),
                        contentAlignment = Alignment.Center
                    ) {
                        Text(
                            text = activeDragLetter?.toString() ?: "",
                            color = localPanelColor,
                            fontSize = 38.sp,
                            fontWeight = FontWeight.Bold
                        )
                    }
                }
            }
        }
    }
}

@OptIn(ExperimentalAnimationApi::class, ExperimentalFoundationApi::class)
@Composable
fun DashboardPortrait(vm: MusicViewModel, panelColor: Color, textMain: Color, textSub: Color, isDark: Boolean) {
    val coroutineScope = rememberCoroutineScope()
    var isListMode by remember { mutableStateOf(false) }
    val fractionAnim = remember { Animatable(0f) }
    var showSettings by remember { mutableStateOf(false) }
    var dragAccumulator by remember { mutableStateOf(0f) }

    LaunchedEffect(isListMode) {
        val target = if (isListMode) 1f else 0f
        if (fractionAnim.targetValue != target) fractionAnim.animateTo(target, tween(350, easing = SnappyDecelerateEasing))
    }

    val dragModifier = Modifier.safeHorizontalSwipe(
        onDrag = { deltaX ->
            dragAccumulator += deltaX
            coroutineScope.launch {
                val d = -deltaX / 600f
                fractionAnim.snapTo((fractionAnim.value + d).coerceIn(0f, 1f))
            }
        },
        onDragEnd = { totalX ->
            val target = if (isListMode) !(totalX > 80f || fractionAnim.value < 0.5f) else (totalX < -80f || fractionAnim.value > 0.5f)
            isListMode = target
            coroutineScope.launch { fractionAnim.animateTo(if (target) 1f else 0f, tween(350, easing = SnappyDecelerateEasing)) }
            dragAccumulator = 0f
        }
    )

    Box(Modifier.fillMaxSize().then(dragModifier)) {
        DynamicFluidBackground(vm.currentSong?.albumArtUri, vm.lrcAlpha, isDark)
        val fraction = fractionAnim.value

        Column(Modifier.fillMaxSize().padding(24.dp).graphicsLayer { translationX = -200f * fraction }, horizontalAlignment = Alignment.CenterHorizontally) {
            Spacer(Modifier.height(40.dp))

            Crossfade(targetState = vm.currentSong, animationSpec = tween(400), label = "portrait_info_fade") { song: Song? ->
                Column(horizontalAlignment = Alignment.CenterHorizontally, modifier = Modifier.fillMaxWidth().padding(horizontal = 16.dp)) {
                    Text(text = song?.title ?: "QwePlayer", color = textMain, fontSize = 28.sp, fontWeight = FontWeight.Bold, maxLines = 1, overflow = TextOverflow.Ellipsis)
                    Text(text = song?.artist ?: "请吩咐或点击播放", color = textSub, fontSize = 16.sp, maxLines = 1, overflow = TextOverflow.Ellipsis)
                }
            }

            Box(modifier = Modifier.weight(1f).fillMaxWidth().padding(vertical = 16.dp)) {
                Box(modifier = Modifier.fillMaxSize().padding(horizontal = 18.dp)) {
                    Crossfade(targetState = vm.currentLyrics, animationSpec = tween(400), label = "lyrics_fade") { lyrics ->
                        LyricEngineView(lyrics = lyrics, vm = vm, fontSize = vm.lrcSize, spacing = vm.lrcSpacing, textColor = textMain)
                    }
                }
            }
            SharedPlaybackControls(vm = vm, textMain = textMain, textSub = textSub, panelColor = panelColor, isDark = isDark, isListMode = isListMode, onTogglePlaylistMode = { isListMode = !isListMode })
        }

        Box(
            Modifier
                .align(Alignment.CenterEnd)
                .fillMaxHeight()
                .fillMaxWidth(0.85f)
                .graphicsLayer {
                    val f = fractionAnim.value
                    translationX = (1f - f) * size.width
                    alpha = f
                }
                .background(panelColor)
        ) {
            PlaylistComponent(vm = vm, textMain = textMain, textSub = textSub, isDark = isDark, onOpenSettings = { showSettings = true }, modifier = Modifier.fillMaxSize().padding(16.dp))
        }
    }
    SettingsPanel(vm, showSettings, { showSettings = false }, panelColor, textMain, textSub)
}

@OptIn(ExperimentalAnimationApi::class)
@Composable
fun DashboardLandscape(vm: MusicViewModel, panelColor: Color, textMain: Color, textSub: Color, isDark: Boolean) {
    val coroutineScope = rememberCoroutineScope()
    var isListMode by remember { mutableStateOf(vm.defaultShowPlaylist) }
    val fractionAnim = remember { Animatable(if (isListMode) 1f else 0f) }
    var showSettings by remember { mutableStateOf(false) }
    var dragAccumulator by remember { mutableStateOf(0f) }

    LaunchedEffect(isListMode) {
        val target = if (isListMode) 1f else 0f
        if (fractionAnim.targetValue != target) fractionAnim.animateTo(target, tween(350, easing = SnappyDecelerateEasing))
    }

    val dragModifier = Modifier.safeHorizontalSwipe(
        onDrag = { deltaX ->
            dragAccumulator += deltaX
            coroutineScope.launch {
                val d = -deltaX / 1200f
                fractionAnim.snapTo((fractionAnim.value + d).coerceIn(0f, 1f))
            }
        },
        onDragEnd = { totalX ->
            val target = if (isListMode) !(totalX > 80f || fractionAnim.value < 0.5f) else (totalX < -80f || fractionAnim.value > 0.5f)
            isListMode = target
            coroutineScope.launch { fractionAnim.animateTo(if (target) 1f else 0f, tween(350, easing = SnappyDecelerateEasing)) }
            dragAccumulator = 0f
        }
    )

    val musicNotePainter = rememberVectorPainter(Icons.Rounded.MusicNote)

    Box(Modifier.fillMaxSize().then(dragModifier)) {
        DynamicFluidBackground(vm.currentSong?.albumArtUri, vm.lrcAlpha, isDark)
        Box(Modifier.fillMaxSize().background(Brush.verticalGradient(colors = if (isDark) listOf(Color.Black.copy(alpha = 0.18f), Color.Transparent, Color.Black.copy(alpha = 0.28f)) else listOf(Color.White.copy(alpha = 0.12f), Color.Transparent, Color.White.copy(alpha = 0.20f)))))

        BoxWithConstraints(Modifier.fillMaxSize().padding(horizontal = 32.dp, vertical = 24.dp)) {
            val totalWidth = maxWidth
            val totalHeight = maxHeight
            val fraction = fractionAnim.value

            val leftWeight = lerpFloat(1.0f, 1.1f, fraction)
            val rightWeight = lerpFloat(1.3f, 1.1f, fraction)
            val spacerW = lerpDp(64.dp, 48.dp, fraction)

            val leftWidth = (totalWidth - spacerW) * (leftWeight / (leftWeight + rightWeight))
            val rightWidth = totalWidth - leftWidth - spacerW
            val controlsHeight = 140.dp
            val leftTopHeight = totalHeight - controlsHeight

            Box(Modifier.align(Alignment.BottomStart).width(leftWidth)) {
                SharedPlaybackControls(vm = vm, textMain = textMain, textSub = textSub, panelColor = panelColor, isDark = isDark, isListMode = isListMode, onTogglePlaylistMode = { isListMode = !isListMode })
            }

            val playlistOffsetX = leftWidth + spacerW + ((rightWidth + 64.dp) * (1f - fraction))
            Box(Modifier.offset(x = playlistOffsetX, y = 0.dp).width(rightWidth).fillMaxHeight()) {
                PlaylistComponent(vm = vm, textMain = textMain, textSub = textSub, isDark = isDark, onOpenSettings = { showSettings = true }, modifier = Modifier.fillMaxSize())
            }

            val maxArtSize = min(leftWidth.value * 0.7f, leftTopHeight.value * 0.65f).dp
            val minArtSize = 90.dp
            val artSize = lerpDp(maxArtSize, minArtSize, fraction)

            val artXImm = (leftWidth - maxArtSize) / 2f
            val artYImm = (leftTopHeight - maxArtSize - 80.dp) / 2f
            val artX = lerpDp(artXImm, 0.dp, fraction)
            val artY = lerpDp(artYImm, 0.dp, fraction)

            Box(modifier = Modifier.offset(x = artX, y = artY)) {
                Crossfade(targetState = vm.currentSong?.albumArtUri, animationSpec = tween(400), label = "art_fade") { uri ->
                    Box(
                        modifier = Modifier
                            .size(artSize)
                            .clip(RoundedCornerShape(20.dp))
                            .border(1.dp, textMain.copy(alpha = 0.08f), RoundedCornerShape(20.dp))
                    ) {
                        AsyncImage(
                            model = uri,
                            contentDescription = null,
                            placeholder = musicNotePainter,
                            error = musicNotePainter,
                            fallback = musicNotePainter,
                            modifier = Modifier.fillMaxSize(),
                            contentScale = ContentScale.Crop
                        )
                    }
                }
            }

            val textWImm = leftWidth
            val textWList = leftWidth - minArtSize - 16.dp
            val textW = lerpDp(textWImm, textWList, fraction)

            val textXImm = 0.dp
            val textYImm = artYImm + maxArtSize + 20.dp
            val textXList = minArtSize + 16.dp
            val textYList = (minArtSize - 54.dp) / 2f

            val textX = lerpDp(textXImm, textXList, fraction)
            val textY = lerpDp(textYImm, textYList, fraction)

            val titleSize = lerpFloat(32f, 26f, fraction).sp
            val artistSize = lerpFloat(18f, 16f, fraction).sp
            val align = if (fraction < 0.5f) Alignment.CenterHorizontally else Alignment.Start
            val textAlign = if (fraction < 0.5f) TextAlign.Center else TextAlign.Start

            Box(modifier = Modifier.offset(x = textX, y = textY).width(textW)) {
                Crossfade(targetState = vm.currentSong, animationSpec = tween(400), label = "landscape_info_fade") { song: Song? ->
                    Column(modifier = Modifier.fillMaxWidth(), horizontalAlignment = align) {
                        Text(text = song?.title ?: "探索音乐", color = textMain, fontSize = titleSize, fontWeight = FontWeight.Black, maxLines = 1, overflow = TextOverflow.Ellipsis, textAlign = textAlign, modifier = Modifier.fillMaxWidth())
                        Spacer(Modifier.height(4.dp))
                        Text(text = song?.artist ?: "QwePlayer", color = textSub, fontSize = artistSize, maxLines = 1, overflow = TextOverflow.Ellipsis, textAlign = textAlign, modifier = Modifier.fillMaxWidth())
                    }
                }
            }

            val lrcXImm = leftWidth + spacerW
            val lrcYImm = 0.dp
            val lrcWImm = rightWidth
            val lrcHImm = totalHeight

            val lrcXList = 0.dp
            val lrcYList = minArtSize + 16.dp
            val lrcWList = leftWidth
            val lrcHList = leftTopHeight - lrcYList

            val lrcX = lerpDp(lrcXImm, lrcXList, fraction)
            val lrcY = lerpDp(lrcYImm, lrcYList, fraction)
            val lrcW = lerpDp(lrcWImm, lrcWList, fraction)
            val lrcH = lerpDp(lrcHImm, lrcHList, fraction)
            val currentLrcFontSize = lerpFloat(vm.lrcSize, vm.lrcSize - 6f, fraction)

            Box(modifier = Modifier.offset(x = lrcX, y = lrcY).size(width = lrcW, height = lrcH)) {
                Crossfade(targetState = vm.currentLyrics, animationSpec = tween(400), label = "landscape_lyrics_fade") { lyrics ->
                    LyricEngineView(lyrics = lyrics, vm = vm, fontSize = currentLrcFontSize, spacing = vm.lrcSpacing, textColor = textMain)
                }
            }
        }
    }
    SettingsPanel(vm, showSettings, { showSettings = false }, panelColor, textMain, textSub)
}

@Composable
fun SettingsPanel(vm: MusicViewModel, show: Boolean, onDismiss: () -> Unit, panelColor: Color, textMain: Color, textSub: Color) {
    var showRenameDialog by remember { mutableStateOf<CustomPlaylist?>(null) }
    var showSongsManager by remember { mutableStateOf(false) }
    var showLyricsEditor by remember { mutableStateOf(false) }

    AnimatedVisibility(
        visible = show,
        enter = slideInHorizontally(initialOffsetX = { offset: Int -> offset }) + fadeIn(),
        exit = slideOutHorizontally(targetOffsetX = { offset: Int -> offset }) + fadeOut()
    ) {
        Box(Modifier.fillMaxSize().background(Color.Black.copy(0.45f)).clickable { onDismiss() }, contentAlignment = Alignment.CenterEnd) {
            Column(Modifier.fillMaxHeight().fillMaxWidth(0.85f).background(panelColor).clickable(enabled = false) {}.padding(24.dp)) {
                Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                    Text("播放器偏好设置", color = textMain, fontSize = 28.sp, fontWeight = FontWeight.Black)
                    IconButton(onClick = onDismiss, modifier = Modifier.background(textMain.copy(0.1f), CircleShape)) { Icon(Icons.Rounded.Close, null, tint = textMain) }
                }
                Spacer(Modifier.height(16.dp))

                val tabs = listOf("播放", "显示", "媒体库", "歌词", "音效", "关于")
                var selectedTab by remember { mutableIntStateOf(0) }

                ScrollableTabRow(
                    selectedTabIndex = selectedTab,
                    containerColor = Color.Transparent,
                    contentColor = textMain,
                    edgePadding = 0.dp,
                    divider = { HorizontalDivider(color = textMain.copy(0.1f)) },
                    indicator = { tabPositions ->
                        if (selectedTab < tabPositions.size) {
                            TabRowDefaults.Indicator(modifier = Modifier.tabIndicatorOffset(tabPositions[selectedTab]), color = textMain)
                        }
                    }
                ) {
                    tabs.forEachIndexed { index, title ->
                        Tab(
                            selected = selectedTab == index,
                            onClick = { selectedTab = index },
                            text = { Text(text = title, color = if (selectedTab == index) textMain else textSub, fontWeight = if (selectedTab == index) FontWeight.Bold else FontWeight.Normal, fontSize = 15.sp) }
                        )
                    }
                }

                Spacer(Modifier.height(24.dp))

                LazyColumn(modifier = Modifier.weight(1f), verticalArrangement = Arrangement.spacedBy(16.dp)) {
                    item {
                        when (selectedTab) {
                            0 -> {
                                SettingsCardSection("启动与播放行为", textMain) {
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Column(modifier = Modifier.weight(1f)) { Text("启动继续播放", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold); Text("恢复上次未播完的歌曲与进度", color = textSub, fontSize = 13.sp) }
                                        Switch(checked = vm.autoResumePlay, onCheckedChange = { vm.updateSetting("autoResumePlay", it) }, colors = SwitchDefaults.colors(checkedThumbColor = panelColor, checkedTrackColor = textMain))
                                    }
                                    Spacer(Modifier.height(16.dp))
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Column(modifier = Modifier.weight(1f)) { Text("播放时常亮屏幕", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold); Text("当音乐播放时保持屏幕常亮不熄灭", color = textSub, fontSize = 13.sp) }
                                        Switch(checked = vm.keepScreenOn, onCheckedChange = { vm.updateSetting("keepScreenOn", it) }, colors = SwitchDefaults.colors(checkedThumbColor = panelColor, checkedTrackColor = textMain))
                                    }
                                    Spacer(Modifier.height(16.dp))
                                    var sleepMenuExpanded by remember { mutableStateOf(false) }
                                    val sleepOptions = listOf(0 to "关闭", 15 to "15 分钟", 30 to "30 分钟", 45 to "45 分钟", 60 to "60 分钟", 90 to "90 分钟")
                                    val sleepLabel = if (vm.sleepTimerMinutes > 0) "剩余 ${vm.formatSleepTime(vm.sleepTimerRemaining)}" else "关闭"
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Column(modifier = Modifier.weight(1f)) { Text("睡眠定时器", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold); Text("设定时间后自动暂停播放", color = textSub, fontSize = 13.sp) }
                                        Box {
                                            Row(
                                                modifier = Modifier.clip(RoundedCornerShape(8.dp)).background(textMain.copy(0.08f)).clickable { sleepMenuExpanded = true }.padding(horizontal = 12.dp, vertical = 8.dp),
                                                verticalAlignment = Alignment.CenterVertically
                                            ) {
                                                Text(sleepLabel, color = textMain, fontSize = 13.sp, fontWeight = FontWeight.Bold)
                                                Spacer(Modifier.width(4.dp))
                                                Icon(Icons.Rounded.ArrowDropDown, null, tint = textMain, modifier = Modifier.size(18.dp))
                                            }
                                            DropdownMenu(expanded = sleepMenuExpanded, onDismissRequest = { sleepMenuExpanded = false }, modifier = Modifier.background(panelColor, RoundedCornerShape(12.dp))) {
                                                sleepOptions.forEach { (minutes, label) ->
                                                    DropdownMenuItem(
                                                        text = { Text(label, color = if (vm.sleepTimerMinutes == minutes) textMain else textSub, fontSize = 14.sp, fontWeight = if (vm.sleepTimerMinutes == minutes) FontWeight.Bold else FontWeight.Normal) },
                                                        trailingIcon = { if (vm.sleepTimerMinutes == minutes) Icon(Icons.Rounded.Check, null, tint = textMain, modifier = Modifier.size(18.dp)) },
                                                        onClick = { if (minutes == 0) vm.stopSleepTimer() else vm.startSleepTimer(minutes); sleepMenuExpanded = false }
                                                    )
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            1 -> {
                                SettingsCardSection("界面与显示", textMain) {
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Column(modifier = Modifier.weight(1f)) { Text("横屏默认布局", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold); Text("决定启动时是展示列表模式或沉浸模式", color = textSub, fontSize = 13.sp) }
                                        Row(Modifier.background(textMain.copy(0.08f), RoundedCornerShape(12.dp)).padding(4.dp)) {
                                            val isList = vm.defaultShowPlaylist
                                            Box(Modifier.clip(RoundedCornerShape(8.dp)).background(if(!isList) textMain else Color.Transparent).clickable { vm.updateSetting("defaultShowPlaylist", false) }.padding(horizontal = 16.dp, vertical = 8.dp)) { Text("沉浸写真", color = if(!isList) panelColor else textMain, fontSize = 13.sp, fontWeight = FontWeight.Bold) }
                                            Box(Modifier.clip(RoundedCornerShape(8.dp)).background(if(isList) textMain else Color.Transparent).clickable { vm.updateSetting("defaultShowPlaylist", true) }.padding(horizontal = 16.dp, vertical = 8.dp)) { Text("所有列表", color = if(isList) panelColor else textMain, fontSize = 13.sp, fontWeight = FontWeight.Bold) }
                                        }
                                    }
                                    Spacer(Modifier.height(16.dp))
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.spacedBy(12.dp)) {
                                        listOf(0 to "跟随系统", 1 to "纯净白", 2 to "深邃黑").forEach { pair: Pair<Int, String> ->
                                            val v = pair.first; val label = pair.second; val isSel = vm.themeMode == v
                                            Box(modifier = Modifier.weight(1f).height(48.dp).clip(RoundedCornerShape(12.dp)).background(if (isSel) textMain else textMain.copy(0.06f)).clickable { vm.updateSetting("theme", v) }, contentAlignment = Alignment.Center) { Text(label, color = if(isSel) panelColor else textMain, fontSize = 14.sp, fontWeight = FontWeight.Bold) }
                                        }
                                    }
                                }
                            }
                            2 -> { 
                                SettingsCardSection("库状态与操作", textMain) {
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Column(modifier = Modifier.weight(1f)) {
                                            Text("曲库深度扫描", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold)
                                            Text("强制刷新本地媒体库文件与歌单", color = textSub, fontSize = 13.sp)
                                        }
                                        Box(modifier = Modifier.clip(RoundedCornerShape(8.dp)).background(textMain).clickable { vm.scan() }.padding(horizontal = 16.dp, vertical = 8.dp), contentAlignment = Alignment.Center) {
                                            Text("立即扫描", color = panelColor, fontSize = 13.sp, fontWeight = FontWeight.Bold)
                                        }
                                    }
                                    Spacer(Modifier.height(16.dp))
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Column(modifier = Modifier.weight(1f)) {
                                            Text("本地歌曲文件管理", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold)
                                            Text("共有 ${vm.songList.size} 首歌曲", color = textSub, fontSize = 13.sp)
                                        }
                                        Box(modifier = Modifier.clip(RoundedCornerShape(8.dp)).background(textMain.copy(0.08f)).clickable { showSongsManager = true }.padding(horizontal = 16.dp, vertical = 8.dp), contentAlignment = Alignment.Center) {
                                            Text("清理歌曲", color = textMain, fontSize = 13.sp, fontWeight = FontWeight.Bold)
                                        }
                                    }
                                }

                                SettingsCardSection("播放列表设置", textMain) {
                                    var showExcludeDialog by remember { mutableStateOf(false) }
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Column(modifier = Modifier.weight(1f)) {
                                            Text("排除特定歌单", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold)
                                            Text("排除的歌单歌曲不再混入“全部歌曲”中", color = textSub, fontSize = 13.sp)
                                        }
                                        Row(modifier = Modifier.clip(RoundedCornerShape(8.dp)).background(textMain.copy(0.08f)).clickable { showExcludeDialog = true }.padding(horizontal = 12.dp, vertical = 8.dp), verticalAlignment = Alignment.CenterVertically) {
                                            val count = vm.excludePlaylistNames.size
                                            Text(if (count == 0) "无" else "已选 $count 项", color = textMain, fontSize = 13.sp, fontWeight = FontWeight.Bold)
                                            Spacer(Modifier.width(4.dp))
                                            Icon(Icons.Rounded.FilterList, null, tint = textMain, modifier = Modifier.size(18.dp))
                                        }
                                    }

                                    if (showExcludeDialog) {
                                        AlertDialog(
                                            onDismissRequest = { showExcludeDialog = false },
                                            modifier = Modifier.widthIn(max = 360.dp).padding(12.dp),
                                            title = {
                                                Column {
                                                    Text("排除特定歌单", color = textMain, fontSize = 18.sp, fontWeight = FontWeight.Bold)
                                                    Spacer(Modifier.height(4.dp))
                                                    val totalFiltered = vm.getFilteredAllSongs().size
                                                    Text("勾选的歌单将不会出现在「全部歌曲」及随机播放中\n当前全部歌曲有效曲目: $totalFiltered 首", color = textSub, fontSize = 12.sp, lineHeight = 16.sp)
                                                }
                                            },
                                            text = {
                                                if (vm.playlists.isEmpty()) {
                                                    Box(Modifier.fillMaxWidth().padding(24.dp), contentAlignment = Alignment.Center) { Text("暂无可排除的自定义歌单", color = textSub, fontSize = 14.sp) }
                                                } else {
                                                    LazyColumn(modifier = Modifier.heightIn(max = 320.dp), verticalArrangement = Arrangement.spacedBy(6.dp)) {
                                                        items(vm.playlists) { playlist ->
                                                            val isChecked = vm.excludePlaylistNames.contains(playlist.name)
                                                            Row(
                                                                modifier = Modifier.fillMaxWidth().clip(RoundedCornerShape(12.dp)).background(if (isChecked) textMain.copy(0.08f) else Color.Transparent).clickable { vm.toggleExcludePlaylist(playlist.name) }.padding(horizontal = 12.dp, vertical = 10.dp),
                                                                verticalAlignment = Alignment.CenterVertically
                                                            ) {
                                                                Checkbox(checked = isChecked, onCheckedChange = { vm.toggleExcludePlaylist(playlist.name) }, colors = CheckboxDefaults.colors(checkedColor = textMain, checkmarkColor = panelColor, uncheckedColor = textSub))
                                                                Spacer(Modifier.width(10.dp))
                                                                Column(modifier = Modifier.weight(1f)) {
                                                                    Text(text = playlist.name, color = textMain, fontSize = 15.sp, fontWeight = if (isChecked) FontWeight.Bold else FontWeight.Normal)
                                                                    Text(text = "${playlist.songs.size} 首歌曲", color = textSub, fontSize = 12.sp)
                                                                }
                                                                if (isChecked) {
                                                                    Text(text = "已排除", color = Color(0xFFFF5252), fontSize = 12.sp, fontWeight = FontWeight.Bold)
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            },
                                            confirmButton = { TextButton(onClick = { showExcludeDialog = false }) { Text("完成", color = textMain, fontSize = 15.sp, fontWeight = FontWeight.Bold) } },
                                            containerColor = panelColor, shape = RoundedCornerShape(22.dp)
                                        )
                                    }

                                    Spacer(Modifier.height(16.dp))
                                    Text("自定义歌单管理", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold, modifier = Modifier.padding(bottom = 8.dp))

                                    if (vm.playlists.filter { it.name != vm.FAVORITE_PLAYLIST_NAME }.isEmpty()) {
                                        Text("暂无自定义歌单", color = textSub, fontSize = 13.sp)
                                    } else {
                                        vm.playlists.filter { it.name != vm.FAVORITE_PLAYLIST_NAME }.forEach { p ->
                                            Row(Modifier.fillMaxWidth().padding(vertical = 4.dp), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                                Text(p.name, color = textSub, fontSize = 14.sp)
                                                Row(horizontalArrangement = Arrangement.spacedBy(8.dp)) {
                                                    IconButton(onClick = { showRenameDialog = p }, modifier = Modifier.size(32.dp)) { Icon(Icons.Rounded.Edit, null, tint = textMain, modifier = Modifier.size(18.dp)) }
                                                    IconButton(onClick = { vm.deletePlaylist(p) }, modifier = Modifier.size(32.dp)) { Icon(Icons.Rounded.Delete, null, tint = Color(0xFFFF5252), modifier = Modifier.size(18.dp)) }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            3 -> {
                                SettingsCardSection("歌词元数据编辑", textMain) {
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Column(modifier = Modifier.weight(1f).padding(end = 12.dp)) {
                                            Text("当前播放歌曲", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold)
                                            Text(vm.currentSong?.title ?: "无", color = textSub, fontSize = 13.sp, maxLines = 1, overflow = TextOverflow.Ellipsis)
                                        }
                                        Box(modifier = Modifier.clip(RoundedCornerShape(8.dp)).background(if(vm.currentSong != null) textMain.copy(0.08f) else Color.Transparent).clickable(enabled = vm.currentSong != null) { showLyricsEditor = true }.padding(horizontal = 16.dp, vertical = 8.dp), contentAlignment = Alignment.Center) {
                                            Text("查看/修改歌词", color = if(vm.currentSong != null) textMain else textSub, fontSize = 13.sp, fontWeight = FontWeight.Bold)
                                        }
                                    }
                                }
                                SettingsCardSection("沉浸与歌词调优", textMain) {
                                    var fontMenuExpanded by remember { mutableStateOf(false) }
                                    val fontOptions = listOf(
                                        0 to "系统默认", 1 to "古典衬线", 2 to "等宽代码", 3 to "手写艺术", 4 to "无衬线体",
                                        5 to "萝莉体", 6 to "阿里普惠体", 7 to "方正行楷", 8 to "德彪钢笔行书", 9 to "草莓体", 10 to "剪纸体"
                                    )
                                    val currentFontLabel = fontOptions.find { pair: Pair<Int, String> -> pair.first == vm.lrcFont }?.second ?: "系统默认"

                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Text("歌词字体样式", color = textMain, fontSize = 15.sp, fontWeight = FontWeight.Bold)
                                        Box {
                                            Spacer(Modifier.width(1.dp))
                                            Row(modifier = Modifier.clip(RoundedCornerShape(8.dp)).background(textMain.copy(0.08f)).clickable { fontMenuExpanded = true }.padding(horizontal = 12.dp, vertical = 8.dp), verticalAlignment = Alignment.CenterVertically) {
                                                Text(currentFontLabel, color = textMain, fontSize = 13.sp, fontWeight = FontWeight.Bold)
                                                Spacer(Modifier.width(4.dp))
                                                Icon(Icons.Rounded.ArrowDropDown, null, tint = textMain, modifier = Modifier.size(18.dp))
                                            }

                                            DropdownMenu(expanded = fontMenuExpanded, onDismissRequest = { fontMenuExpanded = false }, modifier = Modifier.background(panelColor, RoundedCornerShape(12.dp))) {
                                                fontOptions.forEach { pair: Pair<Int, String> ->
                                                    val v = pair.first; val label = pair.second
                                                    DropdownMenuItem(
                                                        text = { Text(label, color = if (vm.lrcFont == v) textMain else textSub, fontSize = 14.sp, fontWeight = if (vm.lrcFont == v) FontWeight.Bold else FontWeight.Normal) },
                                                        trailingIcon = { if (vm.lrcFont == v) Icon(Icons.Rounded.Check, null, tint = textMain, modifier = Modifier.size(18.dp)) },
                                                        onClick = { vm.updateSetting("lrcFont", v); fontMenuExpanded = false }
                                                    )
                                                }
                                            }
                                        }
                                    }
                                    Spacer(Modifier.height(16.dp))
                                    SettingsSliderRow("背景遮罩强度", "${(vm.lrcAlpha.coerceIn(0f, 1f) * 100).toInt()}%", vm.lrcAlpha, 0f..1f, { value: Float -> vm.updateSetting("lrcAlpha", value) }, textMain, textSub, panelColor)
                                    Spacer(Modifier.height(8.dp))
                                    SettingsSliderRow("歌词字号大小", "${vm.lrcSize.toInt()}pt", vm.lrcSize, 20f..52f, { value: Float -> vm.updateSetting("lrcSize", value) }, textMain, textSub, panelColor)
                                    Spacer(Modifier.height(8.dp))
                                    SettingsSliderRow("歌词行距", "${vm.lrcSpacing.toInt()}pt", vm.lrcSpacing, 0f..40f, { value: Float -> vm.updateSetting("lrcSpacing", value) }, textMain, textSub, panelColor)
                                }
                            }
                            4 -> {
                                SettingsCardSection("全局声场控制", textMain) {
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Column(modifier = Modifier.weight(1f)) { Text("统一歌曲音量", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold); Text("自动平衡不同平台下载歌曲的音量大小差异", color = textSub, fontSize = 13.sp) }
                                        Switch(checked = vm.unifiedLoudness, onCheckedChange = { vm.updateSetting("unifiedLoudness", it) }, colors = SwitchDefaults.colors(checkedThumbColor = panelColor, checkedTrackColor = textMain))
                                    }
                                    Spacer(Modifier.height(16.dp))
                                    Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                        Column(modifier = Modifier.weight(1f)) { Text("音效增强", color = textMain, fontSize = 16.sp, fontWeight = FontWeight.Bold); Text("开启专业音效均衡器与声场效果", color = textSub, fontSize = 13.sp) }
                                        Switch(checked = vm.eqEnabled, onCheckedChange = { vm.toggleEqEnabled(it) }, colors = SwitchDefaults.colors(checkedThumbColor = panelColor, checkedTrackColor = textMain))
                                    }

                                    if (vm.eqEnabled) {
                                        Spacer(Modifier.height(16.dp))
                                        var reverbMenuExpanded by remember { mutableStateOf(false) }
                                        val currentReverbLabel = vm.reverbPresets.getOrNull(vm.reverbPreset) ?: "无"
                                        Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                            Text("混响效果", color = textMain, fontSize = 15.sp, fontWeight = FontWeight.Bold)
                                            Box {
                                                Row(modifier = Modifier.clip(RoundedCornerShape(8.dp)).background(textMain.copy(0.08f)).clickable { reverbMenuExpanded = true }.padding(horizontal = 12.dp, vertical = 8.dp), verticalAlignment = Alignment.CenterVertically) {
                                                    Text(currentReverbLabel, color = textMain, fontSize = 13.sp, fontWeight = FontWeight.Bold)
                                                    Spacer(Modifier.width(4.dp))
                                                    Icon(Icons.Rounded.ArrowDropDown, null, tint = textMain, modifier = Modifier.size(18.dp))
                                                }
                                                DropdownMenu(expanded = reverbMenuExpanded, onDismissRequest = { reverbMenuExpanded = false }, modifier = Modifier.background(panelColor, RoundedCornerShape(12.dp))) {
                                                    vm.reverbPresets.forEachIndexed { index, name ->
                                                        DropdownMenuItem(
                                                            text = { Text(name, color = if (vm.reverbPreset == index) textMain else textSub, fontSize = 14.sp, fontWeight = if (vm.reverbPreset == index) FontWeight.Bold else FontWeight.Normal) },
                                                            trailingIcon = { if (vm.reverbPreset == index) Icon(Icons.Rounded.Check, null, tint = textMain, modifier = Modifier.size(18.dp)) },
                                                            onClick = { vm.updateReverbPreset(index); reverbMenuExpanded = false }
                                                        )
                                                    }
                                                }
                                            }
                                        }

                                        Spacer(Modifier.height(16.dp))
                                        SettingsSliderRow(
                                            "虚拟环绕", "${vm.virtualizerStrength}%",
                                            vm.virtualizerStrength.toFloat(), 0f..1000f,
                                            { value -> vm.setVirtualizer(value.toInt()) },
                                            textMain, textSub, panelColor
                                        )
                                    }
                                }
                            }
                            5 -> {
                                Column(modifier = Modifier.fillMaxWidth(), horizontalAlignment = Alignment.CenterHorizontally) {
                                    Box(Modifier.size(80.dp).clip(RoundedCornerShape(20.dp)).background(textMain.copy(0.08f)), contentAlignment = Alignment.Center) {
                                        Icon(Icons.Rounded.MusicNote, contentDescription = null, tint = textMain, modifier = Modifier.size(48.dp))
                                    }
                                    Spacer(Modifier.height(16.dp))
                                    Text("QwePlayer", color = textMain, fontSize = 24.sp, fontWeight = FontWeight.Black)
                                    Text("v1.0.0", color = textSub, fontSize = 14.sp)
                                    Spacer(Modifier.height(8.dp))
                                    Text("一款纯粹的安卓本地音乐播放器", color = textSub, fontSize = 14.sp)

                                    Spacer(Modifier.height(32.dp))

                                    SettingsCardSection("数据统计", textMain) {
                                        Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                            Text("今日听歌时长", color = textMain, fontSize = 15.sp, fontWeight = FontWeight.Bold)
                                            Text(vm.formatListenTime(vm.todayListenTimeMs), color = textSub, fontSize = 14.sp, fontWeight = FontWeight.Medium)
                                        }
                                        Spacer(Modifier.height(12.dp))
                                        Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                            Text("累计听歌总时长", color = textMain, fontSize = 15.sp, fontWeight = FontWeight.Bold)
                                            Text(vm.formatListenTime(vm.totalListenTimeMs), color = textSub, fontSize = 14.sp, fontWeight = FontWeight.Medium)
                                        }
                                    }

                                    Spacer(Modifier.height(16.dp))

                                    SettingsCardSection("开源与许可", textMain) {
                                        Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                            Text("开放源码许可", color = textMain, fontSize = 15.sp, fontWeight = FontWeight.Bold)
                                            Text("Apache-2.0 license", color = textSub, fontSize = 14.sp, fontWeight = FontWeight.Medium)
                                        }
                                        Spacer(Modifier.height(12.dp))
                                        Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                                            Text("开源项目地址", color = textMain, fontSize = 15.sp, fontWeight = FontWeight.Bold)
                                            Text("https://Github.com/Qwejay/QwePlayer", color = textSub, fontSize = 14.sp, fontWeight = FontWeight.Medium)
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    if (showRenameDialog != null) {
        var newName by remember { mutableStateOf(showRenameDialog!!.name) }
        AlertDialog(
            onDismissRequest = { showRenameDialog = null }, modifier = Modifier.widthIn(max = 340.dp).padding(12.dp),
            title = { Text("重命名歌单", color = textMain, fontSize = 18.sp, fontWeight = FontWeight.Bold) },
            text = { OutlinedTextField(value = newName, onValueChange = { newName = it }, textStyle = TextStyle(color = textMain, fontSize = 14.sp), singleLine = true) },
            confirmButton = { TextButton(onClick = { vm.renamePlaylist(showRenameDialog!!, newName); showRenameDialog = null }) { Text("确定", color = textMain) } },
            dismissButton = { TextButton(onClick = { showRenameDialog = null }) { Text("取消", color = textSub) } }, containerColor = panelColor, shape = RoundedCornerShape(22.dp)
        )
    }

    if (showLyricsEditor) {
        var editedLyrics by remember(vm.rawLyricsText) { mutableStateOf(vm.rawLyricsText) }
        AlertDialog(
            onDismissRequest = { showLyricsEditor = false }, modifier = Modifier.widthIn(max = 480.dp).padding(12.dp),
            title = { Text("修改歌词", color = textMain, fontSize = 18.sp, fontWeight = FontWeight.Bold) },
            text = {
                OutlinedTextField(
                    value = editedLyrics, onValueChange = { editedLyrics = it },
                    textStyle = TextStyle(color = textMain, fontSize = 12.sp, lineHeight = 18.sp),
                    modifier = Modifier.fillMaxWidth().height(300.dp)
                )
            },
            confirmButton = { TextButton(onClick = { vm.saveCustomLyrics(vm.currentSong, editedLyrics); showLyricsEditor = false }) { Text("保存", color = textMain) } },
            dismissButton = { TextButton(onClick = { showLyricsEditor = false }) { Text("取消", color = textSub) } }, containerColor = panelColor, shape = RoundedCornerShape(22.dp)
        )
    }

    if (showSongsManager) {
        AlertDialog(
            onDismissRequest = { showSongsManager = false }, modifier = Modifier.widthIn(max = 400.dp).padding(12.dp),
            title = { Text("清理本地歌曲", color = textMain, fontSize = 18.sp, fontWeight = FontWeight.Bold) },
            text = {
                LazyColumn(
                    modifier = Modifier.heightIn(max = 400.dp),
                    contentPadding = PaddingValues(top = 8.dp, bottom = 24.dp)
                ) {
                    itemsIndexed(items = vm.songList, key = { index, song -> "${song.id}_$index" }) { index, song ->
                        Row(Modifier.fillMaxWidth().padding(vertical = 6.dp), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                            Column(Modifier.weight(1f).padding(end = 8.dp)) {
                                Text(song.title, color = textMain, fontSize = 14.sp, maxLines = 1, overflow = TextOverflow.Ellipsis)
                                Text(song.artist, color = textSub, fontSize = 11.sp, maxLines = 1, overflow = TextOverflow.Ellipsis)
                            }
                            IconButton(onClick = { vm.deleteLocalSong(song) }, modifier = Modifier.size(32.dp)) {
                                Icon(Icons.Rounded.Delete, null, tint = Color(0xFFFF5252), modifier = Modifier.size(18.dp))
                            }
                        }
                    }
                }
            },
            confirmButton = { TextButton(onClick = { showSongsManager = false }) { Text("关闭", color = textMain) } },
            containerColor = panelColor, shape = RoundedCornerShape(22.dp)
        )
    }
}

@Composable
fun SettingsCardSection(title: String, textMain: Color, content: @Composable ColumnScope.() -> Unit) {
    Column(modifier = Modifier.fillMaxWidth().clip(RoundedCornerShape(24.dp)).background(textMain.copy(0.04f)).padding(20.dp)) {
        Text(title, color = textMain.copy(0.6f), fontSize = 13.sp, fontWeight = FontWeight.Bold, modifier = Modifier.padding(bottom = 12.dp))
        content()
    }
}

@Composable
fun SettingsSliderRow(title: String, valueLabel: String, value: Float, range: ClosedFloatingPointRange<Float>, onValueChange: (Float) -> Unit, textMain: Color, textSub: Color, panelColor: Color) {
    Column(modifier = Modifier.fillMaxWidth()) {
        Row(Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
            Text(title, color = textMain, fontSize = 15.sp, fontWeight = FontWeight.Bold)
            Box(Modifier.background(textMain, RoundedCornerShape(8.dp)).padding(horizontal = 8.dp, vertical = 4.dp)) { Text(valueLabel, color = panelColor, fontSize = 12.sp, fontWeight = FontWeight.Bold) }
        }
        Slider(value = value, onValueChange = onValueChange, valueRange = range, colors = SliderDefaults.colors(thumbColor = textMain, activeTrackColor = textMain, inactiveTrackColor = textMain.copy(alpha = 0.15f)))
    }
}

// ==========================================
// 10. 本地 UDP 接收器与程序入口
// ==========================================
class LocalControlServer(private val vm: MusicViewModel) {
    private var udpSocket: DatagramSocket? = null
    private var isRunning = false
    private val scope = CoroutineScope(Dispatchers.IO + SupervisorJob())

    private var lastCmd = ""
    private var lastCmdTime = 0L
    private val debounceDelay = 800L

    fun start() {
        if (isRunning) return
        isRunning = true
        scope.launch {
            try {
                udpSocket = DatagramSocket(8888)
                val buffer = ByteArray(256)
                while (isRunning) {
                    val packet = DatagramPacket(buffer, buffer.size)
                    udpSocket?.receive(packet)
                    val msg = String(packet.data, 0, packet.length).trim()

                    val now = System.currentTimeMillis()
                    if (msg == "ping") continue
                    if (msg == lastCmd && (now - lastCmdTime) < debounceDelay) continue

                    lastCmd = msg
                    lastCmdTime = now

                    scope.launch(Dispatchers.Main) {
                        when (msg) {
                            "voice_start" -> vm.startPressTalk()
                            "voice_stop"  -> vm.stopPressTalk()
                            "next_song"   -> vm.nextMusic()
                            "pause"       -> vm.togglePlayPause()
                        }
                    }
                }
            } catch (_: Exception) {}
        }
    }

    fun stop() {
        isRunning = false
        udpSocket?.close()
        scope.cancel()
    }
}

class MainActivity : ComponentActivity() {
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContent {
            QwePlayerTheme {
                val vm: MusicViewModel = viewModel()

                DisposableEffect(Unit) {
                    val localServer = LocalControlServer(vm)
                    localServer.start()
                    onDispose { localServer.stop() }
                }

                KeepScreenOnEffect(keep = vm.keepScreenOn, isPlaying = vm.isPlaying)

                val perm = rememberLauncherForActivityResult(ActivityResultContracts.RequestMultiplePermissions()) { result ->
                    val audioGranted = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) result[Manifest.permission.READ_MEDIA_AUDIO] == true else result[Manifest.permission.READ_EXTERNAL_STORAGE] == true
                    val micGranted = result[Manifest.permission.RECORD_AUDIO] == true
                    if (audioGranted) vm.checkAndScan()
                    if (micGranted) vm.voiceManager?.start() else vm.voiceFeedback = "麦克风未开启，语音不可用"
                }

                LaunchedEffect(Unit) {
                    val permissions = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) arrayOf(Manifest.permission.RECORD_AUDIO, Manifest.permission.READ_MEDIA_AUDIO) else arrayOf(Manifest.permission.RECORD_AUDIO, Manifest.permission.READ_EXTERNAL_STORAGE)
                    perm.launch(permissions)
                }

                Surface(modifier = Modifier.fillMaxSize(), color = Color.Black) { AppRouter(vm) }
            }
        }
    }
}