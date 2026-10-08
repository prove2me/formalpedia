-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_19
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:26:17.845096+00:00
-- url     : https://prove2.me/submissions/b7884a1b-afeb-470e-a18c-2c843f4d1e0f

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval3.At19. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 19

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt19 (d : ℚ) : ℚ :=
  -4029455493699599872 + d * (-752883089176025856 + d * (1731441136084258176 + d *
    (-3799636202425164864 + d * (5556285178742932992 + d * (-3295290811462761600 + d *
    (-1023903848588222016 + d * (4251306961072328256 + d * (-5915790813281410368 + d *
    (5950743438335342272 + d * (-4145471978841866304 + d * (1690335507310718976))))))))))) + d ^
    12 * (397180477994018880 + d * (-1882726581740737728 + d * (2703461629605777792 + d *
    (-2841612387828122112 + d * (2510244399952602240 + d * (-1980081647318765952 + d *
    (1420814131281261952 + d * (-932559024546749760 + d * (567268652510180352 + d *
    (-323277629672798592 + d * (171255883229784000 + d * (-83219999647693248))))))))))) + d ^ 12
    * (37328119090444992 + d * (-15769993723292736 + d * (6230643980534592 + d *
    (-2195058813831872 + d * (669763238865984 + d * (-193186333527360 + d * (63274010197440 + d
    * (-22191650140608 + d * (6347185201344 + d * (-1280300252736 + d * (241244493888 + d *
    (-83533406784))))))))))) + d ^ 12 * (29132982336 + d * (-5478861120 + d * (384346944 + d *
    (-61625536 + d * (49121856 + d * (-10592448 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt19 (d : ℚ) : ℚ :=
  -4775385538888700736 + d * (-960874702677026368 + d * (2622488556309948928 + d *
    (-6080630612967939840 + d * (9545635792973556032 + d * (-7987828356445991488 + d *
    (3011051030093725056 + d * (1228257103445416064 + d * (-4307682934203337344 + d *
    (6428668853763573952 + d * (-6392958712026266240 + d * (4804824064463147520))))))))))) + d ^
    12 * (-2860788248367251264 + d * (1023632182811458240 + d * (401669166215513472 + d *
    (-1109201528236120192 + d * (1208423419983840320 + d * (-1017887033970566272 + d *
    (746839442856009088 + d * (-495815288838068480 + d * (311079198755115008 + d *
    (-191361532995635328 + d * (114650879247627776 + d * (-65635824697622528))))))))))) + d ^ 12
    * (36188230308749632 + d * (-19508690283751488 + d * (10192643606513408 + d *
    (-5071370629014528 + d * (2395677495286720 + d * (-1075510975608000 + d * (453542633918592 +
    d * (-177197417627776 + d * (64233257070912 + d * (-21708563637632 + d * (6668693740928 + d
    * (-1738196876288))))))))))) + d ^ 12 * (347292292096 + d * (-45036751360 + d * (1988874240
    + d * (387211264 + d * (-52389888 + d * (-1341440 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt19 (d : ℚ) : ℚ :=
  13483539722436651642787286843372737559964579679492636672 + d *
    (-619352767856419071892005804470484435383310873803089772544 + d *
    (121969486779047961327376963546055370094551752430514601984 + d *
    (1540761844655435140581652125946974518471136662185724870656 + d *
    (-3026457381111996803184464284073465203325175671291409334272 + d *
    (3755301389239961250228757488295906166821712544896484376576 + d *
    (-4737095884421849715277981644003129324054536212176437248 + d *
    (-9052319969975677638915008219923367261181211175492859723776 + d *
    (18180511528249507639163580300419870440962044449825837809664 + d *
    (-20231801257981882560976558677424774434255059147353366200320 + d *
    (8771425298538101872576621527745987964896643944302255800320 + d *
    (17469119423189651584111480390499696224991926642725248303104))))))))))) + d ^ 12 *
    (-48686933142965321500933141543268596827856652934616357273600 + d *
    (67245696583266900535815922340235162864566855471132675145728 + d *
    (-57250615973682543609736598169710177464168828371834881179648 + d *
    (12597135587453072540491015130208686238903453222838033448960 + d *
    (57086654786749220824498593929501235492631767902883516776448 + d *
    (-127001575219171133714162030495728730915555715822848517603328 + d *
    (167243814264919551955748435015342333656535385387741378248704 + d *
    (-155959818172020269454166027808113293623804249168463116894208 + d *
    (88885306886995568295967122645251056550189212376260412964864 + d *
    (17568906090465301982237593752988211387384838987559744045056 + d *
    (-131644458692813952660449778728192825006773529503492618846208 + d *
    (218198392113056198464898455888522226368318769928913257496576))))))))))) + d ^ 12 *
    (-251302284202858355029561455843387701870865981963471980331008 + d *
    (222413665460419061986629431383026979372891761663358217486336 + d *
    (-141922130627658875429282862688398596415095818165686808346624 + d *
    (34095651094117192353248085504156766302856521398038597992448 + d *
    (72025120015903918092266376715303654958882090297001296789504 + d *
    (-151795935161665763580445330241902375266655883424109681180672 + d *
    (191114381653297572433343360518216805158918237043359831818240 + d *
    (-188276945142771807490603418830994614652441448466042437500928 + d *
    (151873300561135437637217186352628754503441168485752207572992 + d *
    (-96262898601894441210522661971388808757026238448327227867136 + d *
    (36630629178399300846931351991993080467519038485378543910912 + d *
    (14833835101093282498970558618271168621493198770724502241280))))))))))) + d ^ 12 *
    (-50915014259159069827051781149508924574952646284873102262272 + d *
    (69532054089394390824444362727751199861948728519990647455744 + d *
    (-72611308306282868354800155689926271603659859590725984845824 + d *
    (64394562467897164248504226648664695050854115735969063501824 + d *
    (-49802101880804867344597404781156666844390141977372552331264 + d *
    (33222771771858923192369072738451584403026390847791736553472 + d *
    (-17856007468638748948963474430106003931273013686517343977472 + d *
    (5546949513688276793093094976929813463969606836253890969600 + d *
    (3041630448308329174817595952102047604607640020663166042112 + d *
    (-8092560509667179256334304301413932490567129138166794027008 + d *
    (10269924158715397736247723489548266989161025532116095729664 + d *
    (-10412711031611217983811560607423014875313047365240105730048))))))))))) + d ^ 12 *
    (9323315636226468350598464588013357638671260398522081738752 + d *
    (-7651747677349303260764340127728032761184217937628047081472 + d *
    (5856261318536642612058398552586376864045525394060209291264 + d *
    (-4214315845970513505925719939183334375482184404194659401728 + d *
    (2859491085801472450902623769800220854130136317467371241472 + d *
    (-1825900497679363678288635452410865309414821918730079436800 + d *
    (1088664069542029855535734978065790936813732175278164672512 + d *
    (-595103867996436174318339443764895896648981431402990403584 + d *
    (285607650645101007554918792508177735953287401235008716800 + d *
    (-105539987047703215194236471055466830606826730693485133824 + d *
    (10557661808348265152177220021219404433178461408136527872 + d *
    (32285548599832198703409930447593412062723282388737327104))))))))))) + d ^ 12 *
    (-45710666039659085033206499880438058603158292235310071808 + d *
    (44315921795564716826017050788946348388011423762531483648 + d *
    (-36797228188517696832155604479860925974412024773250383872 + d *
    (27876683680717254474507389096947556261762661535749767168 + d *
    (-19792632996765275914060546621844615306282565280298696704 + d *
    (13353908634274265133352858117972345970911648359128498176 + d *
    (-8629878032485287592448242777996192963630224215097737216 + d *
    (5367870485514082522856138663242161704728071050340073472 + d *
    (-3223496461898145963087915540590182348706931727122563072 + d *
    (1872423772114699880523447288366549724783710291946635264 + d *
    (-1053180232122930884840195540763137454584523340917768192 + d *
    (573872969846357064177041202675170242043839822131101696))))))))))) + d ^ 12 *
    (-302894718675408433276802052135884636963718223485992960 + d *
    (154750366836363158995020056774762316982907400376811520 + d *
    (-76427787313119056596378249324386803013304660875804672 + d *
    (36407694063576081250462553056248630013182894357348352 + d *
    (-16670898810483744024108064328474188762992469078704128 + d *
    (7297725561487844682308722251581516070257798241320960 + d *
    (-3026923440787554497238800272070382488739998231166976 + d *
    (1170935478189295234705933124062488699478593707966464 + d *
    (-409244886084536640887788625453001872883540261339136 + d *
    (119310490158062648743039023534586240601699317186560 + d *
    (-20724032979657356800799543646686283307545596002304 + d *
    (-6333653344799138225990230203936109711587215409152))))))))))) + d ^ 12 *
    (9833323360664846987070579218231587159014482378752 + d *
    (-7344356489024038173644055046330093739862552477696 + d *
    (4439913621239358084349531099531650058360026562560 + d *
    (-2400436372135175525373394940282357556461231407104 + d *
    (1204518344864856922480070099334523351557962203136 + d *
    (-571022319637999681369623435376498544837884379136 + d *
    (258239910660988501557136187203663842788345905152 + d *
    (-112047766033364597839532813276875678746776698880 + d *
    (46805500397568874739165941892622857108928856064 + d *
    (-18862781846453619987189293410339741491894943744 + d *
    (7342156895379113091233670426075942788047044608 + d *
    (-2761488092390633403399829016418423429067440128))))))))))) + d ^ 12 *
    (1003490250616107596373278351756251829692006400 + d *
    (-352103901661939250936165026673723327131942912 + d *
    (119167882877297723383747192105698835783745536 + d *
    (-38844671947427646993851069689866243928227840 + d *
    (12171306830059056728842743850479214469840896 + d *
    (-3656670148053963786981182364975543503290368 + d *
    (1049989885866134068858744876796874689347584 + d *
    (-286985183631549358569491727462789279645696 + d *
    (74275381392253255618253244090851016048640 + d * (-18082029857992741838593555901831092633600
    + d * (4105110920196171234327190939685232312320 + d *
    (-859259009618721334551512731118779498496))))))))))) + d ^ 12 *
    (163235935513697802306007557656730140672 + d * (-27502096995644132531875154930278596608 + d
    * (3957334921668747295216364355452403712 + d * (-451582578890828002963750657842479104 + d *
    (32936857272058642884007709215031296 + d * (397364765680417231153532115615744 + d *
    (-528731641708542439944422964854784 + d * (76398998369791131897347344695296 + d *
    (-4708987361303173020383454167040 + d * (205698863406589251509944320000 + d *
    (-156074183280605528530926174208 + d * (54907520294373606592200310784))))))))))) + d ^ 12 *
    (-9383309663961848771500310528 + d * (721795680562194710426025984 + d *
    (35808086615858315281825792 + d * (-14831927859427419727069184 + d *
    (1367146633668072474148864 + d * (-7659524005805596868608 + d * (-6873028352207802859520 + d
    * (171358841137224744960 + d * (11768424844360679424 + d * (4836226696846770176 + d *
    (-309423326351065088 + d * (-55609798016106496))))))))))) + d ^ 12 * (1603888855646208 + d *
    (345104795303936 + d * (16128712900608 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt19 (d : ℚ) : ℚ :=
  966816828821359870754710012498383857872363613 + d *
    (-44254793385458872775560786927569249779510917925 + d *
    (1349402075208562918269962127646034631592138221 + d *
    (124784197211854012869008635218452952579449177501 + d *
    (-207279103773298493102475005782448648585303771392 + d *
    (197863597861948021254505220520956929376265772763 + d *
    (129134117474480421235176449741261022988159605283 + d *
    (-742684248246626644987923482953965791816782179476 + d *
    (1179262541457369680890233501237296134196313903068 + d *
    (-969701772258576163387053864595445479695325462434 + d *
    (-108437612898426452811707476866665650790793630222 + d *
    (1825852893556745652574364009570033925382285341761))))))))))) + d ^ 12 *
    (-3314945295572715658258130857920846314932846314576 + d *
    (3510325705478039183779412880544502294124625891282 + d *
    (-1854179464454178260587925468737681794097369690277 + d *
    (-1388001812311634223216399161960110134321221370274 + d *
    (5125559812071685805915308029194728991538250138662 + d *
    (-7798920886259603222113161403408495658098183119352 + d *
    (8105689641861106844937401591788601264387794679497 + d *
    (-5613847022567475551178120379457384704675137588927 + d *
    (929774330877612612414102406087627152170906496135 + d *
    (4525551655357656601728949040452672273910484417079 + d *
    (-9045354164881662261780979243863708540210751903945 + d *
    (11281085634600289666427399621105938047121208504146))))))))))) + d ^ 12 *
    (-10685418274173299451148598171985734331010472656604 + d *
    (7600181126119711593940112346344714149561979569968 + d *
    (-3040042149756891602155802708355540654628609737629 + d *
    (-1709145126493149257449818610340042605576438916227 + d *
    (5515443316507689323255744049644876812326800519531 + d *
    (-7689900103706354948868340409935806709610366983069 + d *
    (8074987016976038293713917623469726105400616659610 + d *
    (-6962217994601023133504212878722628726589946393755 + d *
    (4908270627445813053541952092595408911527800466001 + d *
    (-2529502751389728743213448356194153127819251460377 + d *
    (341564387779469833403111157624732920920131898952 + d *
    (1325554512656391923484849573966052904739771689828))))))))))) + d ^ 12 *
    (-2340878946662950373225156843386709486990750667258 + d *
    (2735462273374217704743321818035254398862562032356 + d *
    (-2641635255112697706981235536729742704089249445987 + d *
    (2232006761798548072703083254529882678090328872400 + d *
    (-1672607228940157844863463961041845855967364097975 + d *
    (1094984846640495720648577546027016586863963333357 + d *
    (-585729189622605355490988308398265673665838594763 + d *
    (188679625173263576678897866375997881112407646543 + d *
    (85807484158974742857727413432473690164278821296 + d *
    (-249303408280779956941149263606357699123729879853 + d *
    (324623532923155043371737352264312958205156065311 + d *
    (-337640899446745638350107333101460128417432750623))))))))))) + d ^ 12 *
    (312044294149136744383107863347979875570405391882 + d *
    (-266716460655966144461877757910919722272550425211 + d *
    (215042232964848394921918476487701516427486635859 + d *
    (-165403139811432322418914194262654705348378940298 + d *
    (122233851739430647201734127151846007913923939259 + d *
    (-87200787073805323139735134865107136902008535795 + d *
    (60248763141367672694315054559313841614809989904 + d *
    (-40408237066646079785159564500285105251032279014 + d *
    (26350191699642835384461800338329044624494551240 + d *
    (-16725099433057174150177246328899748901296597051 + d *
    (10340331605664309145119571646485379679534103704 + d *
    (-6229509733931579568318164978543017223710029341))))))))))) + d ^ 12 *
    (3657491390302067712118526630156036074217517271 + d *
    (-2092543465211265277252027395631842191811391712 + d *
    (1166212752476991884973450687879976284373464155 + d *
    (-632756941638322567012037543684428495408715229 + d *
    (333943795987195498555864447421324602394571055 + d *
    (-171221100310757087766137501704535088870174214 + d *
    (85144661575901115530300208429070443586441581 + d *
    (-40969194879590867498005533538861969627479841 + d *
    (19011325060132375407604518017169561416181430 + d *
    (-8466246021457523912623458019411941867627729 + d *
    (3590663733621231802863524000607455104863829 + d *
    (-1431812713266041887807962288838581265058093))))))))))) + d ^ 12 *
    (523998128178208337652209082934605329819176 + d *
    (-166651307329107419109619657746263006895754 + d *
    (38611701898607789140815038868097155505547 + d * (455796229783734174830871816622832415815 +
    d * (-8404634365616850772954633740397435180040 + d *
    (7322887495457254702044554981521840698431 + d * (-4723992375320048944871996244398709731638 +
    d * (2657201561808179514446079172113191980670 + d *
    (-1372379645811163621364398154168865178809 + d * (665894579288008920169339065712125829285 +
    d * (-307203286458740807773671870374672810315 + d *
    (135681454240925304351272987766888314082))))))))))) + d ^ 12 *
    (-57606033853175315024721685254369997662 + d * (23567611825435561261409838481644021487 + d *
    (-9303129510584411870041647943756288158 + d * (3545142075014812082561593069266839081 + d *
    (-1304031371699733088141506003458384990 + d * (462710772045741122647712169407526937 + d *
    (-158186428764022090384547080317606688 + d * (52009274135146060969252113386391021 + d *
    (-16405932500108057185495755497122264 + d * (4950193013540543771215934987870556 + d *
    (-1423337803682313888250493933681567 + d * (388072899464495262134385347055998))))))))))) + d
    ^ 12 * (-99649663463226987725778519023201 + d * (23868638139150024686140436157744 + d *
    (-5262457786059101382106435248222 + d * (1048830781759117946021276643281 + d *
    (-184358836253213662570077124252 + d * (27582438593751271954397216746 + d *
    (-3314277441545161491873175330 + d * (283553789595114057505169878 + d *
    (-11247750110475966064371659 + d * (-654736238151292695956598 + d * (42223148428497919375806
    + d * (16206375276686259383565))))))))))) + d ^ 12 * (572256968101719418654 + d *
    (-1542792995266562637864 + d * (402179430565277283332 + d * (-52549294293373234203 + d *
    (3013830332858890447 + d * (128474789338014653 + d * (-31073264475908299 + d *
    (1172164499293496 + d * (14427508278695 + d * (11104873172471 + d * (-595668588397 + d *
    (-173975894029))))))))))) + d ^ 12 * (5055203149 + d * (1234473012 + d * (58451986 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_19 (d : ℚ) :
    orderSevenSelectionPolynomial d 19 = selectionExpandedAt19 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 19 =
      selectionNumeratorAt19 d := by
    unfold pointTateParameterUnivariateNumerator
      pointTateAlphaUnivariateCleared
      pointTateCompletedTangentNumerator
      Doubling.completedCubic
      orderSevenQuotient
      orderSevenB
      orderSevenC
      WeierstrassCurve.b₂
      WeierstrassCurve.b₄
      WeierstrassCurve.b₆
      selectionNumeratorAt19
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 19 =
      selectionDenominatorAt19 d := by
    unfold pointTateParameterUnivariateDenominator
      pointTateGammaUnivariateCleared
      pointTateAlphaUnivariateCleared
      pointTateCompletedTangentNumerator
      Doubling.completedCubic
      orderSevenQuotient
      orderSevenB
      orderSevenC
      WeierstrassCurve.b₂
      WeierstrassCurve.b₄
      WeierstrassCurve.b₆
      selectionDenominatorAt19
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt19 selectionDenominatorAt19 selectionExpandedAt19
  ring

private theorem selection_cofactor_eval_at_19 (d : ℚ) :
    (selectionCofactor d).eval 19 = selectionCofactorAt19 d := by
  simp only [selectionCofactor, selectionCofactorData,
    Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  unfold
    Internal.selectionCofactorCoefficient0
    Internal.selectionCofactorCoefficient0Chunk0
    Internal.selectionCofactorCoefficient0Chunk1
    Internal.selectionCofactorCoefficient0Chunk2
    Internal.selectionCofactorCoefficient0Chunk3
    Internal.selectionCofactorCoefficient0Chunk4
    Internal.selectionCofactorCoefficient0Chunk5
    Internal.selectionCofactorCoefficient0Chunk6
    Internal.selectionCofactorCoefficient0Chunk7
    Internal.selectionCofactorCoefficient0Chunk8
    Internal.selectionCofactorCoefficient0Chunk9
    Internal.selectionCofactorCoefficient0Chunk10
    Internal.selectionCofactorCoefficient1
    Internal.selectionCofactorCoefficient1Chunk0
    Internal.selectionCofactorCoefficient1Chunk1
    Internal.selectionCofactorCoefficient1Chunk2
    Internal.selectionCofactorCoefficient1Chunk3
    Internal.selectionCofactorCoefficient1Chunk4
    Internal.selectionCofactorCoefficient1Chunk5
    Internal.selectionCofactorCoefficient1Chunk6
    Internal.selectionCofactorCoefficient1Chunk7
    Internal.selectionCofactorCoefficient1Chunk8
    Internal.selectionCofactorCoefficient1Chunk9
    Internal.selectionCofactorCoefficient1Chunk10
    Internal.selectionCofactorCoefficient2
    Internal.selectionCofactorCoefficient2Chunk0
    Internal.selectionCofactorCoefficient2Chunk1
    Internal.selectionCofactorCoefficient2Chunk2
    Internal.selectionCofactorCoefficient2Chunk3
    Internal.selectionCofactorCoefficient2Chunk4
    Internal.selectionCofactorCoefficient2Chunk5
    Internal.selectionCofactorCoefficient2Chunk6
    Internal.selectionCofactorCoefficient2Chunk7
    Internal.selectionCofactorCoefficient2Chunk8
    Internal.selectionCofactorCoefficient2Chunk9
    Internal.selectionCofactorCoefficient3
    Internal.selectionCofactorCoefficient3Chunk0
    Internal.selectionCofactorCoefficient3Chunk1
    Internal.selectionCofactorCoefficient3Chunk2
    Internal.selectionCofactorCoefficient3Chunk3
    Internal.selectionCofactorCoefficient3Chunk4
    Internal.selectionCofactorCoefficient3Chunk5
    Internal.selectionCofactorCoefficient3Chunk6
    Internal.selectionCofactorCoefficient3Chunk7
    Internal.selectionCofactorCoefficient3Chunk8
    Internal.selectionCofactorCoefficient3Chunk9
    Internal.selectionCofactorCoefficient4
    Internal.selectionCofactorCoefficient4Chunk0
    Internal.selectionCofactorCoefficient4Chunk1
    Internal.selectionCofactorCoefficient4Chunk2
    Internal.selectionCofactorCoefficient4Chunk3
    Internal.selectionCofactorCoefficient4Chunk4
    Internal.selectionCofactorCoefficient4Chunk5
    Internal.selectionCofactorCoefficient4Chunk6
    Internal.selectionCofactorCoefficient4Chunk7
    Internal.selectionCofactorCoefficient4Chunk8
    Internal.selectionCofactorCoefficient4Chunk9
    Internal.selectionCofactorCoefficient5
    Internal.selectionCofactorCoefficient5Chunk0
    Internal.selectionCofactorCoefficient5Chunk1
    Internal.selectionCofactorCoefficient5Chunk2
    Internal.selectionCofactorCoefficient5Chunk3
    Internal.selectionCofactorCoefficient5Chunk4
    Internal.selectionCofactorCoefficient5Chunk5
    Internal.selectionCofactorCoefficient5Chunk6
    Internal.selectionCofactorCoefficient5Chunk7
    Internal.selectionCofactorCoefficient5Chunk8
    Internal.selectionCofactorCoefficient5Chunk9
    Internal.selectionCofactorCoefficient6
    Internal.selectionCofactorCoefficient6Chunk0
    Internal.selectionCofactorCoefficient6Chunk1
    Internal.selectionCofactorCoefficient6Chunk2
    Internal.selectionCofactorCoefficient6Chunk3
    Internal.selectionCofactorCoefficient6Chunk4
    Internal.selectionCofactorCoefficient6Chunk5
    Internal.selectionCofactorCoefficient6Chunk6
    Internal.selectionCofactorCoefficient6Chunk7
    Internal.selectionCofactorCoefficient6Chunk8
    Internal.selectionCofactorCoefficient7
    Internal.selectionCofactorCoefficient7Chunk0
    Internal.selectionCofactorCoefficient7Chunk1
    Internal.selectionCofactorCoefficient7Chunk2
    Internal.selectionCofactorCoefficient7Chunk3
    Internal.selectionCofactorCoefficient7Chunk4
    Internal.selectionCofactorCoefficient7Chunk5
    Internal.selectionCofactorCoefficient7Chunk6
    Internal.selectionCofactorCoefficient7Chunk7
    Internal.selectionCofactorCoefficient7Chunk8
    Internal.selectionCofactorCoefficient8
    Internal.selectionCofactorCoefficient8Chunk0
    Internal.selectionCofactorCoefficient8Chunk1
    Internal.selectionCofactorCoefficient8Chunk2
    Internal.selectionCofactorCoefficient8Chunk3
    Internal.selectionCofactorCoefficient8Chunk4
    Internal.selectionCofactorCoefficient8Chunk5
    Internal.selectionCofactorCoefficient8Chunk6
    Internal.selectionCofactorCoefficient8Chunk7
    Internal.selectionCofactorCoefficient8Chunk8
    Internal.selectionCofactorCoefficient9
    Internal.selectionCofactorCoefficient9Chunk0
    Internal.selectionCofactorCoefficient9Chunk1
    Internal.selectionCofactorCoefficient9Chunk2
    Internal.selectionCofactorCoefficient9Chunk3
    Internal.selectionCofactorCoefficient9Chunk4
    Internal.selectionCofactorCoefficient9Chunk5
    Internal.selectionCofactorCoefficient9Chunk6
    Internal.selectionCofactorCoefficient9Chunk7
    Internal.selectionCofactorCoefficient10
    Internal.selectionCofactorCoefficient10Chunk0
    Internal.selectionCofactorCoefficient10Chunk1
    Internal.selectionCofactorCoefficient10Chunk2
    Internal.selectionCofactorCoefficient10Chunk3
    Internal.selectionCofactorCoefficient10Chunk4
    Internal.selectionCofactorCoefficient10Chunk5
    Internal.selectionCofactorCoefficient10Chunk6
    Internal.selectionCofactorCoefficient10Chunk7
    Internal.selectionCofactorCoefficient11
    Internal.selectionCofactorCoefficient11Chunk0
    Internal.selectionCofactorCoefficient11Chunk1
    Internal.selectionCofactorCoefficient11Chunk2
    Internal.selectionCofactorCoefficient11Chunk3
    Internal.selectionCofactorCoefficient11Chunk4
    Internal.selectionCofactorCoefficient11Chunk5
    Internal.selectionCofactorCoefficient11Chunk6
    Internal.selectionCofactorCoefficient11Chunk7
    Internal.selectionCofactorCoefficient12
    Internal.selectionCofactorCoefficient12Chunk0
    Internal.selectionCofactorCoefficient12Chunk1
    Internal.selectionCofactorCoefficient12Chunk2
    Internal.selectionCofactorCoefficient12Chunk3
    Internal.selectionCofactorCoefficient12Chunk4
    Internal.selectionCofactorCoefficient12Chunk5
    Internal.selectionCofactorCoefficient12Chunk6
    Internal.selectionCofactorCoefficient13
    Internal.selectionCofactorCoefficient13Chunk0
    Internal.selectionCofactorCoefficient13Chunk1
    Internal.selectionCofactorCoefficient13Chunk2
    Internal.selectionCofactorCoefficient13Chunk3
    Internal.selectionCofactorCoefficient13Chunk4
    Internal.selectionCofactorCoefficient13Chunk5
    Internal.selectionCofactorCoefficient13Chunk6
    Internal.selectionCofactorCoefficient14
    Internal.selectionCofactorCoefficient14Chunk0
    Internal.selectionCofactorCoefficient14Chunk1
    Internal.selectionCofactorCoefficient14Chunk2
    Internal.selectionCofactorCoefficient14Chunk3
    Internal.selectionCofactorCoefficient14Chunk4
    Internal.selectionCofactorCoefficient14Chunk5
    Internal.selectionCofactorCoefficient14Chunk6
    Internal.selectionCofactorCoefficient15
    Internal.selectionCofactorCoefficient15Chunk0
    Internal.selectionCofactorCoefficient15Chunk1
    Internal.selectionCofactorCoefficient15Chunk2
    Internal.selectionCofactorCoefficient15Chunk3
    Internal.selectionCofactorCoefficient15Chunk4
    Internal.selectionCofactorCoefficient15Chunk5
    Internal.selectionCofactorCoefficient15Chunk6
    Internal.selectionCofactorCoefficient16
    Internal.selectionCofactorCoefficient16Chunk0
    Internal.selectionCofactorCoefficient16Chunk1
    Internal.selectionCofactorCoefficient16Chunk2
    Internal.selectionCofactorCoefficient16Chunk3
    Internal.selectionCofactorCoefficient16Chunk4
    Internal.selectionCofactorCoefficient16Chunk5
    Internal.selectionCofactorCoefficient17
    Internal.selectionCofactorCoefficient17Chunk0
    Internal.selectionCofactorCoefficient17Chunk1
    Internal.selectionCofactorCoefficient17Chunk2
    Internal.selectionCofactorCoefficient17Chunk3
    Internal.selectionCofactorCoefficient17Chunk4
    Internal.selectionCofactorCoefficient17Chunk5
    Internal.selectionCofactorCoefficient18
    Internal.selectionCofactorCoefficient18Chunk0
    Internal.selectionCofactorCoefficient18Chunk1
    Internal.selectionCofactorCoefficient18Chunk2
    Internal.selectionCofactorCoefficient18Chunk3
    Internal.selectionCofactorCoefficient18Chunk4
    Internal.selectionCofactorCoefficient18Chunk5
    Internal.selectionCofactorCoefficient19
    Internal.selectionCofactorCoefficient19Chunk0
    Internal.selectionCofactorCoefficient19Chunk1
    Internal.selectionCofactorCoefficient19Chunk2
    Internal.selectionCofactorCoefficient19Chunk3
    Internal.selectionCofactorCoefficient19Chunk4
    Internal.selectionCofactorCoefficient20
    Internal.selectionCofactorCoefficient20Chunk0
    Internal.selectionCofactorCoefficient20Chunk1
    Internal.selectionCofactorCoefficient20Chunk2
    Internal.selectionCofactorCoefficient20Chunk3
    Internal.selectionCofactorCoefficient20Chunk4
    Internal.selectionCofactorCoefficient21
    Internal.selectionCofactorCoefficient21Chunk0
    Internal.selectionCofactorCoefficient21Chunk1
    Internal.selectionCofactorCoefficient21Chunk2
    Internal.selectionCofactorCoefficient21Chunk3
    Internal.selectionCofactorCoefficient21Chunk4
    Internal.selectionCofactorCoefficient22
    Internal.selectionCofactorCoefficient22Chunk0
    Internal.selectionCofactorCoefficient22Chunk1
    Internal.selectionCofactorCoefficient22Chunk2
    Internal.selectionCofactorCoefficient22Chunk3
    Internal.selectionCofactorCoefficient23
    Internal.selectionCofactorCoefficient23Chunk0
    Internal.selectionCofactorCoefficient23Chunk1
    Internal.selectionCofactorCoefficient23Chunk2
    Internal.selectionCofactorCoefficient23Chunk3
    Internal.selectionCofactorCoefficient24
    Internal.selectionCofactorCoefficient24Chunk0
    Internal.selectionCofactorCoefficient24Chunk1
    Internal.selectionCofactorCoefficient24Chunk2
    Internal.selectionCofactorCoefficient24Chunk3
    Internal.selectionCofactorCoefficient25
    Internal.selectionCofactorCoefficient25Chunk0
    Internal.selectionCofactorCoefficient25Chunk1
    Internal.selectionCofactorCoefficient25Chunk2
    Internal.selectionCofactorCoefficient26
    Internal.selectionCofactorCoefficient26Chunk0
    Internal.selectionCofactorCoefficient26Chunk1
    Internal.selectionCofactorCoefficient26Chunk2
    Internal.selectionCofactorCoefficient27
    Internal.selectionCofactorCoefficient27Chunk0
    Internal.selectionCofactorCoefficient27Chunk1
    Internal.selectionCofactorCoefficient27Chunk2
    Internal.selectionCofactorCoefficient28
    Internal.selectionCofactorCoefficient28Chunk0
    Internal.selectionCofactorCoefficient28Chunk1
    Internal.selectionCofactorCoefficient29
    Internal.selectionCofactorCoefficient29Chunk0
    Internal.selectionCofactorCoefficient29Chunk1
    Internal.selectionCofactorCoefficient30
    Internal.selectionCofactorCoefficient30Chunk0
    Internal.selectionCofactorCoefficient30Chunk1
    Internal.selectionCofactorCoefficient31
    Internal.selectionCofactorCoefficient31Chunk0
    Internal.selectionCofactorCoefficient32
    Internal.selectionCofactorCoefficient32Chunk0
    Internal.selectionCofactorCoefficient33
    Internal.selectionCofactorCoefficient33Chunk0
    selectionCofactorAt19
  simp
  ring

private theorem selection_factor_at_19 (d : ℚ) :
    selectionExpandedAt19 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 19 *
        selectionCofactorAt19 d := by
  unfold selectionExpandedAt19 orderSevenDualKernelPolynomial selectionCofactorAt19
  ring

theorem selectionEvalAt19 (d : ℚ) :
    Internal.SelectionEvalCertificate d 19 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_19, selection_cofactor_eval_at_19,
    selection_factor_at_19]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 19 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt19 d
#print axioms solution
