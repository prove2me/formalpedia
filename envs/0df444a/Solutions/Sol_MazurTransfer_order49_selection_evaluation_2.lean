-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:14:35.512023+00:00
-- url     : https://prove2.me/submissions/325a37ae-d931-4bf0-8399-d2ffffd20c70

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval0.At2. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 2

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt2 (d : ℚ) : ℚ :=
  -11239424 + d * (-96940032 + d * (505247232 + d * (1656356800 + d * (-20642600832 + d *
    (71012562432 + d * (16574787264 + d * (-1424104354176 + d * (8710519466880 + d *
    (-34700188641728 + d * (107811568925760 + d * (-278898822990144))))))))))) + d ^ 12 *
    (621211477869632 + d * (-1215834255336768 + d * (2119100086240128 + d * (-3319168370904384 +
    d * (4701159682470528 + d * (-6044944965669696 + d * (7071404424308608 + d *
    (-7529994032442240 + d * (7292306423667648 + d * (-6406463606834112 + d * (5084281225249536
    + d * (-3623746250734080))))))))))) + d ^ 12 * (2301973923943104 + d * (-1291372808329152 +
    d * (634240937136384 + d * (-272681757830336 + d * (105364174999680 + d * (-39223744375872 +
    d * (15065534022720 + d * (-5743759697664 + d * (1920866044032 + d * (-527624571648 + d *
    (137301692544 + d * (-45110176512))))))))))) + d ^ 12 * (15451100544 + d * (-3636300480 + d
    * (494291520 + d * (-98169280 + d * (46693440 + d * (-10631616 + d * (326592 + d * (122496 +
    d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt2 (d : ℚ) : ℚ :=
  -13271040 + d * (-140027904 + d * (1036519424 + d * (-386497536 + d * (-19915395072 + d *
    (116792713216 + d * (-318418909184 + d * (103748419072 + d * (3306568876544 + d *
    (-18809454328448 + d * (67690579488128 + d * (-190251208649280))))))))))) + d ^ 12 *
    (447314409143808 + d * (-908857232393600 + d * (1625270844232448 + d * (-2588779299101760 +
    d * (3707706291166144 + d * (-4819638709377472 + d * (5748674913966272 + d *
    (-6374723578837440 + d * (6664088328258816 + d * (-6640338309476672 + d * (6331235550025856
    + d * (-5749693512543360))))))))))) + d ^ 12 * (4924533983999424 + d * (-3937035298225984 +
    d * (2914835683430528 + d * (-1986900872397440 + d * (1240305133635136 + d *
    (-704855110348352 + d * (362306331108672 + d * (-167196537182912 + d * (68542789945920 + d *
    (-24533648491904 + d * (7458932503424 + d * (-1847934575616))))))))))) + d ^ 12 *
    (349169979904 + d * (-43843781120 + d * (2015456256 + d * (363571200 + d * (-54774784 + d *
    (-1358848 + d * (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt2 (d : ℚ) : ℚ :=
  242907521692366536704 + d * (18455417102793309159424 + d * (-341043664051152862838784 + d *
    (-8725262183837382838583296 + d * (72230206065804424480030720 + d *
    (583198315870206036134592512 + d * (-8911711951473350146057568256 + d *
    (20510324125760639552412712960 + d * (323521733887766209746469650432 + d *
    (-3133244990270986029280408633344 + d * (9133022089577387799904618545152 + d *
    (45619967806896533544588067471360))))))))))) + d ^ 12 * (-609065672944090990104172657901568
    + d * (2958844334141277869530410285531136 + d * (-4578888185595704561498985296035840 + d *
    (-40432344082171402756080454818594816 + d * (383368870065375553443428411037712384 + d *
    (-1776105265152208706508304285476847616 + d * (4504103080290976893269555249323442176 + d *
    (2626237374298510736794328229117952000 + d * (-96668503860396583714755613981637345280 + d *
    (599403473291124148014308323536342351872 + d * (-2434947148300781816680574288968705114112 +
    d * (6987620365881548713846468028733092003840))))))))))) + d ^ 12 *
    (-10779079480079967894407043389547207196672 + d *
    (-25212129104081002594131795676646037782528 + d *
    (300924508961226257520019251986936241586176 + d *
    (-1600738303513555319829823419529179673133056 + d *
    (6539479079769383728847238185860373539717120 + d *
    (-22831582479238361180571602761047562310123520 + d *
    (71029943851131855827259460078007918224474112 + d *
    (-201128524438975057516569283316354100680458240 + d *
    (524789923977561832585920959547521235287539712 + d *
    (-1271414475129998567859653218418881079911383040 + d *
    (2873491777140093756082650323417108564106805248 + d *
    (-6073360439750496530420976721675612458395893760))))))))))) + d ^ 12 *
    (12009910167297759095508710922128627119982641152 + d *
    (-22177873656415368144537640609920371117708279808 + d *
    (38043754567979892101344644994594067358964252672 + d *
    (-59949540717047957916395372804234731269685510144 + d *
    (84755232288182431914632179801106866551757733888 + d *
    (-101509116382157639826683222361024656554548789248 + d *
    (84368386114322192475636624348998800885952806912 + d *
    (17874035695508234461732375710802851433786900480 + d *
    (-295858909298957467614134861800995364425389309952 + d *
    (896700292904310698752671695785485009285601034240 + d *
    (-2042150546823419498902383991893999161534455742464 + d *
    (4044550721809659408453569164651918161581491355648))))))))))) + d ^ 12 *
    (-7315713673869952797184283855855130279320795742208 + d *
    (12362760239673872685402945441673284660551735312384 + d *
    (-19764693054077544629197221432771649246695910277120 + d *
    (30124664983115119346627681086951014598088100937728 + d *
    (-43995865568661646550311555086219296893014503063552 + d *
    (61783784331003403040331385739680291239654540181504 + d *
    (-83633898044833428444403940140774997783429143330816 + d *
    (109320546568135821285916884184965711534616380964864 + d *
    (-138158307320759115693521639361237390932571282210816 + d *
    (168959620881532230266294893203375236395898800177152 + d *
    (-200059981833488498946933626634529137261654179053568 + d *
    (229423710682046361447214049043230488977987417669632))))))))))) + d ^ 12 *
    (-254829604041580261233832003000199707339942023659520 + d *
    (274118815021342614667405375920079997966712757026816 + d *
    (-285470896021346783911273218357485770387343540224000 + d *
    (287662525435730456465698781798655779121751447568384 + d *
    (-280260942582429838699272957778779858353713926373376 + d *
    (263712470708579818294046472979265893217923274375168 + d *
    (-239304763562423107492826764372597337908532749533184 + d *
    (209005690795009401572051158207351356347749746868224 + d *
    (-175206257527194388619682976950477999591655124238336 + d *
    (140413550642480192546582490521832892815016618360832 + d *
    (-106947888752844450100774843122484288176871104577536 + d *
    (76694451253150238228460596279280666015066141229056))))))))))) + d ^ 12 *
    (-50945234263650186087015427753219843302208660570112 + d *
    (30346402940428791862037333185746795335747506274304 + d *
    (-14944429904230423534865020237382404689463114989568 + d *
    (4306955861880364127302970161255433433871766257664 + d *
    (2315464226340627833088918864970705891813050286080 + d *
    (-5821604529798820032045600290230870685893456035840 + d *
    (7114282214654958155103193146133489162467970383872 + d *
    (-6995131189407265321191219269995985534982415450112 + d *
    (6105116754479300315607965803245905733297794187264 + d *
    (-4906513110771298929632054319366989444364747145216 + d *
    (3695809425771131473071544365498012712278868361216 + d *
    (-2634815348102465848184600850487382777447625785344))))))))))) + d ^ 12 *
    (1788345508054554253722186477359799118031794470912 + d *
    (-1159934107873846458648015786036308138681380372480 + d *
    (720689312164572118622918540826792684626825183232 + d *
    (-429612887919186288167612421748034956550776553472 + d *
    (245948539205803241948984672708794383566176518144 + d *
    (-135294699467633172939913596379905417404221227008 + d *
    (71526714661765164282587523911953400577844576256 + d *
    (-36338142619583694757677954895388987912293449728 + d *
    (17734119869559261864163258519926851860952514560 + d *
    (-8309060683091223358170792516342081605414944768 + d *
    (3734500708964966839652845988741682834701287424 + d *
    (-1608395577102546165013183686384714388083310592))))))))))) + d ^ 12 *
    (662929454209434410546159987819759943015202816 + d *
    (-261080334427264631250971203362630559800754176 + d *
    (98062363364259667437778646696164500358823936 + d *
    (-35050456550720356349449637222719162350567424 + d *
    (11891021008553215812110556995979280276258816 + d *
    (-3817225402043865803665641190447556550721536 + d *
    (1155326322774603998460725384183898660405248 + d *
    (-328255582445055367982268162800319105073152 + d *
    (87097331173613825074570561748744805810176 + d * (-21443738149176331990217946449082578370560
    + d * (4859516304889294384738780486514597429248 + d *
    (-1003006043526365288433068311291749203968))))))))))) + d ^ 12 *
    (185843040277018933895172555173335662592 + d * (-30259402083896098251189954686235181056 + d
    * (4180990888368072450973506192708993024 + d * (-457962169607927786459297662626430976 + d *
    (32945578050624190867249244211773440 + d * (-76750618096923055330165246656512 + d *
    (-355232545637565755541137047945216 + d * (46372633781184345169923823632384 + d *
    (-2494716060414355997564114567168 + d * (420645105538239515727276015616 + d *
    (-234435955954387258281266511872 + d * (63687833025406857465824280576))))))))))) + d ^ 12 *
    (-9570485113763852374346825728 + d * (660220027189858438883573760 + d *
    (41118692123054783970410496 + d * (-14684878981533309654269952 + d *
    (1356762265233001316876288 + d * (-12289072012992637304832 + d * (-6812902637439108251648 +
    d * (230026948908889669632 + d * (12119006950137266176 + d * (4509193811572031488 + d *
    (-330125029392515072 + d * (-56393251628253184))))))))))) + d ^ 12 * (1581472583516160 + d *
    (344861294985216 + d * (16128623771648 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt2 (d : ℚ) : ℚ :=
  7296209911808 + d * (565662854414336 + d * (-9388137177415680 + d * (-278313377271218176 + d *
    (1766472777595281408 + d * (21074880934148803584 + d * (-240637284982085991424 + d *
    (181194602129708456960 + d * (10752764075874917856360 + d * (-78200861646097687109057 + d *
    (119792341196294701867262 + d * (1807157586231694814044043))))))))))) + d ^ 12 *
    (-15898748105881281999359247 + d * (58423556477113251221017436 + d *
    (4739918541198470870268423 + d * (-1395248532754152113978465122 + d *
    (9301929818794898516154442790 + d * (-34161111497968010947103622290 + d *
    (51561173910535447241244517958 + d * (266342775361596843576774355056 + d *
    (-2615727874650149320064440044090 + d * (12853701239900437835394245736873 + d *
    (-44009212391725326648045947207626 + d * (99699391588851257029514631707816))))))))))) + d ^
    12 * (-38507517513762563588459939658823 + d * (-1052139850667162190385474533237204 + d *
    (7133957612149699537091154571766293 + d * (-32324899368637186715164437401815820 + d *
    (120609646279113134706092171646756477 + d * (-395371961316448420399764176784652817 + d *
    (1173493107010701021477973427022629737 + d * (-3208063577185814017211902581411806532 + d *
    (8167487053748133276829074910471836975 + d * (-19515738832605734195802250065095586681 + d *
    (44019961198968434538063232557353970526 + d *
    (-94157290818439079393710311057286055531))))))))))) + d ^ 12 *
    (191689864612293975853176890771845300310 + d * (-372582834959096732684772362913665221083 + d
    * (693212692419007755487410963962704107818 + d * (-1237426382045976802642009057737790081585
    + d * (2123475532149260194110396087421711709554 + d *
    (-3509227483992202679045468888517433845149 + d * (5593470147521557694613822953513607780455 +
    d * (-8610761440806677041478299963045016104959 + d *
    (12817339414935516384856346209936568056119 + d * (-18466309777443705300398232813831687864897
    + d * (25771797114752084162787298845570734107177 + d *
    (-34863975869941729100794213517233185243923))))))))))) + d ^ 12 *
    (45739665429823959946292714834348429678151 + d * (-58216003644547110003573750299727928862783
    + d * (71896891833191083635374054653926543230836 + d *
    (-86162594234774965243853919993480347362583 + d *
    (100191326463119419276754505272207939635393 + d *
    (-113017503196343685299590678003902963213070 + d *
    (123624804994401619414641838266606031913293 + d *
    (-131064436041655866002064320506854863115830 + d *
    (134581654356647093491543672535100507450945 + d *
    (-133728956386291936634973389650736259072224 + d *
    (128443969646180360843754936495865161784789 + d *
    (-119074945315114766999430160976735120700695))))))))))) + d ^ 12 *
    (106346112612848462758908752376896940357288 + d *
    (-91267008880567134145794410937953389178835 + d * (75001302930167272357016608581973889625704
    + d * (-58718657460909636529611608700194147541973 + d *
    (43455814347770146300107656228118389828564 + d * (-30009828441382067325941683443669286893689
    + d * (18878313942243203088930171173011952691723 + d *
    (-10250986259775077695921031990148950203715 + d * (4046428649050010830197543416954639823105
    + d * (19697627555159255111810652533641577650 + d *
    (-2352387270085844800987389050603444403023 + d *
    (3397639760989603572781015975200156519348))))))))))) + d ^ 12 *
    (-3577974337245954790962185233975049742144 + d * (3249777497389579276296914281021480744841 +
    d * (-2683272794753328518430585501181244495035 + d *
    (2061417555050441849649128607651368954396 + d * (-1491622256866811906685840523558211154450 +
    d * (1023817332469829373606086564942082666337 + d *
    (-669504563896936662171925109531833618948 + d * (418266021926088450670641205296831822712 + d
    * (-250077542851867362017655188276521818286 + d * (143241251849089310767666516004985379231 +
    d * (-78641987485987545205160175661933704313 + d *
    (41388181928485485436116516770420262133))))))))))) + d ^ 12 *
    (-20874921935373811437943580069762164706 + d * (10084507040101673347678339388043337598 + d *
    (-4662188487784156319069624084480157460 + d * (2060262452599247427993013070994160266 + d *
    (-868972208678087290461128968094855082 + d * (349172708737752211245215082123537651 + d *
    (-133368587513460374009390391901565694 + d * (48291759230073152078787932309915192 + d *
    (-16522983124275842527741563632663209 + d * (5321117784115856108231830622942106 + d *
    (-1605342325027680915107331923866153 + d * (451123195460086554869572407974887))))))))))) + d
    ^ 12 * (-117256398293647911994114045695468 + d * (27944861761937576059945952465173 + d *
    (-6039190436210583154841233696748 + d * (1166434080655670790744511372418 + d *
    (-197379749318309178168842734640 + d * (28424773272563822864354546983 + d *
    (-3326874199314577667747980530 + d * (291751827085566896188913624 + d *
    (-16445120660593787323889775 + d * (627303501944686429144889 + d *
    (-129734875504606847769115 + d * (25465133009057366019011))))))))))) + d ^ 12 *
    (1592243466464712271235 + d * (-1778163881083733175222 + d * (416439692203450046934 + d *
    (-52082589007218136553 + d * (2973338491290440724 + d * (119600984898749346 + d *
    (-31130269657269966 + d * (1326372987210268 + d * (16135165741440 + d * (10081405897011 + d
    * (-664014626763 + d * (-176546090063))))))))))) + d ^ 12 * (4979604523 + d * (1233609412 +
    d * (58451527 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_2 (d : ℚ) :
    orderSevenSelectionPolynomial d 2 = selectionExpandedAt2 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 2 =
      selectionNumeratorAt2 d := by
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
      selectionNumeratorAt2
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 2 =
      selectionDenominatorAt2 d := by
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
      selectionDenominatorAt2
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt2 selectionDenominatorAt2 selectionExpandedAt2
  ring

private theorem selection_cofactor_eval_at_2 (d : ℚ) :
    (selectionCofactor d).eval 2 = selectionCofactorAt2 d := by
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
    selectionCofactorAt2
  simp
  ring

private theorem selection_factor_at_2 (d : ℚ) :
    selectionExpandedAt2 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 2 *
        selectionCofactorAt2 d := by
  unfold selectionExpandedAt2 orderSevenDualKernelPolynomial selectionCofactorAt2
  ring

theorem selectionEvalAt2 (d : ℚ) :
    Internal.SelectionEvalCertificate d 2 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_2, selection_cofactor_eval_at_2,
    selection_factor_at_2]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 2 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt2 d
#print axioms solution
