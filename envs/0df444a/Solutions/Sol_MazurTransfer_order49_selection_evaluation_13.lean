-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_13
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:47:02.1946+00:00
-- url     : https://prove2.me/submissions/94d0fa9f-29a1-470d-8e3d-8e29e0f031da

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval2.At13. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 13

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt13 (d : ℚ) : ℚ :=
  -43436029431808000 + d * (-14265977668300800 + d * (44994997555223040 + d *
    (-97908415944385344 + d * (126382822403872896 + d * (-42326920017959040 + d *
    (-133621727833392192 + d * (306135083805975360 + d * (-405930678440063040 + d *
    (377887588832321728 + d * (-197659545554288448 + d * (-74984608840460544))))))))))) + d ^ 12
    * (356367857576195136 + d * (-587607922757578944 + d * (729177903963086976 + d *
    (-764218000738689792 + d * (708712075231661184 + d * (-596099576783256192 + d *
    (459365882551270144 + d * (-326098456907244864 + d * (214708987181699712 + d *
    (-131582711123408256 + d * (74706174474874560 + d * (-39046327032470976))))))))))) + d ^ 12
    * (18820296191478720 + d * (-8407861715605824 + d * (3447377822503104 + d *
    (-1262814899332544 + d * (410736698398656 + d * (-128147659831104 + d * (43550733067968 + d
    * (-15330111272640 + d * (4532927242944 + d * (-1004350755648 + d * (211417012416 + d *
    (-70748667456))))))))))) + d ^ 12 * (24205089216 + d * (-4830750528 + d * (423150912 + d *
    (-74523328 + d * (48264768 + d * (-10606272 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt13 (d : ℚ) : ℚ :=
  -51473730940572096 + d * (-18524379810728896 + d * (67690842932941696 + d *
    (-159964839682227840 + d * (243516212059875776 + d * (-194593254710879296 + d *
    (4753688167304448 + d * (218453137692124160 + d * (-417018634668890112 + d *
    (541475572099524928 + d * (-516062151635044352 + d * (355208895844394880))))))))))) + d ^ 12
    * (-127022627192055488 + d * (-111158003450920256 + d * (301541346483883776 + d *
    (-399018117863729920 + d * (405125473594236992 + d * (-352686096852461440 + d *
    (275620309379653504 + d * (-199167399638230784 + d * (137161814947814144 + d *
    (-91822361923603584 + d * (59747402903468288 + d * (-37550032275766016))))))))))) + d ^ 12 *
    (22781446294225600 + d * (-13332645214351296 + d * (7478149358201984 + d *
    (-3990940262961024 + d * (2016259219438912 + d * (-957476542640064 + d * (423339037374720 +
    d * (-173258628748288 + d * (65534941207872 + d * (-22684038978944 + d * (6951319842176 + d
    * (-1777458329600))))))))))) + d ^ 12 * (347869106176 + d * (-44616851968 + d * (1998256128
    + d * (378867712 + d * (-53231616 + d * (-1347584 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt13 (d : ℚ) : ℚ :=
  16841564443415215342050033497390529187509048180736 + d *
    (-755144592698373542798352416422163899623227063795712 + d *
    (-369066123104931158045526465562317621406307999285248 + d *
    (4189046367057203312918851304169178634574106609057792 + d *
    (-7827873089727825196911248757570624962352197305368576 + d *
    (4321030204547850641865672156852511814362038079848448 + d *
    (21718580065485508918224533131786672014428491620810752 + d *
    (-72195635105578571054500209479609103222621071335227392 + d *
    (108858835720797613693423540793720778565241934170030080 + d *
    (-54359596190509894310507511718787435734121693867147264 + d *
    (-170612045992566020862003411230069370484523351220420608 + d *
    (557192752729683562778603220792708041237125395741147136))))))))))) + d ^ 12 *
    (-900178427350195996373432660016936765961152404509425664 + d *
    (791461808361264544033954195182565675057347350740336640 + d *
    (209167508541362325465054485566513289637785855890817024 + d *
    (-2246323895451888515273501060085912552694066359892443136 + d *
    (4805093187367221629156303467472692987467409948315484160 + d *
    (-6564799571888685473765597567796814824474177689862012928 + d *
    (5715571939600951912134052895840689829423918474803019776 + d *
    (-759270947012979123791156243369479565690605321352380416 + d *
    (-8460461206686211008521513196106482005576363392326696960 + d *
    (19976323684773911870363683471959244941134499997442899968 + d *
    (-29696351948028575934661759468777609068054774105433702400 + d *
    (32457998742639676592877580009930509845928549408799719424))))))))))) + d ^ 12 *
    (-23926764416386679643096967905179307167025770578080432128 + d *
    (2678720850986328890020736760167160288572673758449369088 + d *
    (28410283425698496351237480805368675051485762965555904512 + d *
    (-62196554264627901803872995307806756403137894043225161728 + d *
    (88931354735951664095095652988271221047891945574795837440 + d *
    (-99103602260729842214759620712998610223978525490933399552 + d *
    (86514829915030687469838089786734341405053493447220789248 + d *
    (-50507470607910182951666428600126439401012745266531663872 + d *
    (-3444977748962170553629147469406275291292762098757009408 + d *
    (64986525288745070689257361114674820916470926678280110080 + d *
    (-121527863772081362117017146986852753772565662359034265600 + d *
    (161425328269974117146215785929009963830751164378335674368))))))))))) + d ^ 12 *
    (-176725335114616598872280624927110844794062933497298288640 + d *
    (164746277488873656527094167978673259229325648344248745984 + d *
    (-128209406693299754394307892113567483804635399395835117568 + d *
    (74089026988610834989886085365957406354429323506111741952 + d *
    (-11674834628241711952951553279588611452054004628046479360 + d *
    (-49546423760728991244754687473894989946091355180024725504 + d *
    (101663417144972985951347247016710710700275444418664464384 + d *
    (-139444819851376947058466761352544356756054229988887232512 + d *
    (160691105859961338104935402117574906529966212966305497088 + d *
    (-165943125815972924433478509092196356776067139706624147456 + d *
    (157770035362015517725691526984377799583338509659540291584 + d *
    (-139886969029617871661914070504097517093265230195756367872))))))))))) + d ^ 12 *
    (116315535688313764791730339040065266705875823821838352384 + d *
    (-90727817203268069337224763696893308894364015843045015552 + d *
    (66035451453730825088181600237416982295306584017835655168 + d *
    (-44219357320308101394862387180023611911848409621047541760 + d *
    (26352411064485617394507929266027118030937324147138625536 + d *
    (-12748176685756158490481178461092406777148142412137758720 + d *
    (3169218140677852905940233711248052819326656857929940992 + d *
    (2958516887167229312773001710318559068857991568267673600 + d *
    (-6360460226278917965857218361351475030890768694957834240 + d *
    (7774595434520329215653136696932665102474852125510729728 + d *
    (-7862120326132519537193454763079900841552275212963938304 + d *
    (7161558470626034254008203101706267904893829853925343232))))))))))) + d ^ 12 *
    (-6075893220546190573930593160140109736848564102329532416 + d *
    (4881474197747884287745869587619641455720306086432473088 + d *
    (-3748801023229170033018478767484177614092539927178772480 + d *
    (2767635249161880185745782163380004884795691040082493440 + d *
    (-1971399342510056615387280161393608073761044639928287232 + d *
    (1358016416559076241782858866990404113210625421808500736 + d *
    (-906023488988867299940529812986543036866763763915423744 + d *
    (585925805864683199563879552944578929992408998040829952 + d *
    (-367416818844615623334874099556474387915787177941270528 + d *
    (223375950088765406702306730467490733859232447429083136 + d *
    (-131590403038378010880427424998179864302598933951283200 + d *
    (75031989907815353034616152089526932964704481414742016))))))))))) + d ^ 12 *
    (-41337205017352303405980517978719813255355949523402752 + d *
    (21945564343948768482804924658048339769268964538449920 + d *
    (-11181362604073210081735408335195057567704686850998272 + d *
    (5432642906366562576477125938215171073355810258550784 + d *
    (-2490521460484430831621657481915434558765751424778240 + d *
    (1056688734724670186202603427534810559473942527475712 + d *
    (-398330063131334810146816139695170937565325006733312 + d *
    (119031887986622409834034645365453199926822325977088 + d *
    (-14022593201599289723097087405654527831869473685504 + d *
    (-17085897366491281631531995334215424053145095372800 + d *
    (20503153051114277512527297164817557065823057084416 + d *
    (-15803271799987987651339042926371395083087647866880))))))))))) + d ^ 12 *
    (10289755761522640938500518699518366891014142558208 + d *
    (-6076327345573991637439138333905631391794374377472 + d *
    (3350412012526396494435898046423395896079676080128 + d *
    (-1750421847352252280662656332100079028336873963520 + d *
    (873716204287599992094494347183957549570831155200 + d *
    (-418743400603697757226392297058262231005764255744 + d *
    (193293700590669422622013479858790136404859682816 + d *
    (-86099658896395337808745136441262420469567717376 + d *
    (37048114084194026436973062705285971373178486784 + d *
    (-15406998911680337753363351803346161576172584960 + d *
    (6192377371966859105979391009567685520510943232 + d *
    (-2404410464633870252983239042911199345191419904))))))))))) + d ^ 12 *
    (901230135081260559113947842553922563768844288 + d *
    (-325722339940607002181053822797537754802028544 + d *
    (113342838773446358562296060252086393640058880 + d *
    (-37901180482320742376807945243620239313993728 + d *
    (12150727047277379953024586770448879389769728 + d *
    (-3723764536625235926064555460046015055790080 + d *
    (1087018516600797406716516985058492531343360 + d *
    (-300914372342436251903917537418562652078080 + d *
    (78562167717625658062678344059147554127872 + d * (-19211653555279754453073940198908842475520
    + d * (4362236740771601164695292102543933964288 + d *
    (-909298766096804570944679926787150446592))))))))))) + d ^ 12 *
    (171325852169627991467462377034426875904 + d * (-28525017646773769073124522179665068032 + d
    * (4044843407275674584920487521185955840 + d * (-454363266368146612581323393610022912 + d *
    (32824785373769435652425556296728576 + d * (266834159983675577315196017836032 + d *
    (-472128355492820074953633227341824 + d * (65952480616753747347650599976960 + d *
    (-3886644116971658017901919338496 + d * (275725971796759702095972532224 + d *
    (-183657785941020294041780617216 + d * (58042546335294365267237273600))))))))))) + d ^ 12 *
    (-9448835208651224262547865600 + d * (699606107474925331447283712 + d *
    (37664226663528284124872704 + d * (-14774444670936713858908160 + d *
    (1363715097537971901693952 + d * (-9322031835819576918016 + d * (-6854470344102251331584 + d
    * (191950747845873106944 + d * (11888826388067647488 + d * (4720760945193254912 + d *
    (-316729890367864832 + d * (-55886311055687680))))))))))) + d ^ 12 * (1595977230188544 + d *
    (345018854014976 + d * (16128681443328 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt13 (d : ℚ) : ℚ :=
  3601809151266650613995560456603425871187 + d * (-160650154884426680207900629265153836488953 +
    d * (-118413185128222530482146373882951133041439 + d *
    (942527300148866859282550326567182623293437 + d *
    (-1446452255392275434222715080600740756324396 + d *
    (110713133068651354157227944979256723437469 + d *
    (5656099241656137170481307094064705318693985 + d *
    (-14572489609462795131092200606306585146809318 + d *
    (16995886638248595611766979978724209896099752 + d *
    (1354342105587209253449923919464929449718912 + d *
    (-48635906254971027235511189550080469950512404 + d *
    (110515448446019793677544416718493609324783343))))))))))) + d ^ 12 *
    (-138278491563071551766371054473221650331569320 + d *
    (63110339590121852343244628786903606632393306 + d *
    (160091528752867079708611987765943066285330965 + d *
    (-499381306168338254838950904458873637424244278 + d *
    (812164588203183998367762053834581654781898792 + d *
    (-867175331059414054731658789486118232065911642 + d *
    (438385675254234464186786776565562530193523693 + d *
    (560038372229702461657677155481874330987183881 + d *
    (-1960828130250265463083319076763984415059092243 + d *
    (3318724586105563637010108029752303295395719979 + d *
    (-4015342722537976242625358349940531826762033965 + d *
    (3477877676848256434468365470339229270307837108))))))))))) + d ^ 12 *
    (-1432304739216010051639635422634755251333034522 + d *
    (-1914770799621988138763711061226186298750517630 + d *
    (5851748289978168087127856844159098397502094197 + d *
    (-9324577076435735024178730277685309187018884397 + d *
    (11239735003189329646645304827304979002846091977 + d *
    (-10802424900681370541238089800897376771576958475 + d *
    (7772405008032218242525607644420865398583657986 + d *
    (-2553223718057526683897112720881143193833891549 + d *
    (-3908012376074418064223284031780669799226550231 + d *
    (10367917818918382454360631750639097702035167369 + d *
    (-15595493609121973456710828957327166857926986252 + d *
    (18649069941475611818194663179517228273175236856))))))))))) + d ^ 12 *
    (-19052013623976697531189572804457662306295842474 + d *
    (16837958527041720570534849205429133687006242736 + d *
    (-12477321211900362329209821211855623010638646995 + d *
    (6725373024253191218047733975865642514506377630 + d *
    (-442350021616945677163982931456097335183277891 + d *
    (-5569653195011645640428999118221269575400549183 + d *
    (10683534606152425586152610630904915478189807799 + d *
    (-14506322973509473896900828311012955607294164073 + d *
    (16884470858661868829145145863206111347341031930 + d *
    (-17868898958480464705676554867963590068550257913 + d *
    (17657191292126594074654372003271362578491812717 + d *
    (-16529417417427359747615720037813907417799043461))))))))))) + d ^ 12 *
    (14790156192398392006438949403117126589603793462 + d *
    (-12724201882687801067188647826594070684347988909 + d *
    (10568599477664677420926050657814758037256176199 + d *
    (-8499967047769609011823111707281013124103885550 + d *
    (6633850839827211551381245162731751778886113929 + d *
    (-5032037426024524667153243412233616409386172309 + d *
    (3713965016858342375676084194419690258657442508 + d *
    (-2669185249451279134715475892911007062292883512 + d *
    (1868832594049461587627861421404144770571888370 + d *
    (-1274993757256811975509548681393266384831504771 + d *
    (847598188566946945576585191997897264276451946 + d *
    (-548937908756493187718688340335370546866835811))))))))))) + d ^ 12 *
    (346196242813848650256545568505237374004934233 + d *
    (-212471975335134567196932393604815367361906714 + d *
    (126781937915694909956260937119658378472169709 + d *
    (-73457618050045494380124848900009502436291839 + d *
    (41255977241693368130067196256702233147102753 + d *
    (-22406206063819448938189910347127267963817148 + d *
    (11727615541920236637766597339560878762260821 + d *
    (-5886326489056919815885999500859638325424899 + d *
    (2811261398880578420378348233280668689188212 + d *
    (-1260993108437384101200867643833161987378595 + d *
    (518316548652570982331517749756633191234957 + d *
    (-184633644020862673875122597021330177353907))))))))))) + d ^ 12 *
    (47480848492247640956521118105962187981038 + d * (1242819864292515678680316553073945192156 +
    d * (-13636666328512419012435670636680546823321 + d *
    (13170983564037470736252924005823069086459 + d * (-9478745050245068127674925728213503266356
    + d * (5953825507230193416879029061207904138313 + d *
    (-3433427396321757398012651808021524708572 + d * (1859265341032135617862050900631404195914 +
    d * (-956724347728839485168482657865228805801 + d * (471015106236231978850948497156316456807
    + d * (-222782325734033482905443719117157432891 + d *
    (101487928274874885337087337411477145720))))))))))) + d ^ 12 *
    (-44592520449926311039337038887003686364 + d * (18911237197819749206952663427277064451 + d *
    (-7741615596112265023382404410113519958 + d * (3057947916281321386504521907721079671 + d *
    (-1164544028931348024720754036921751276 + d * (427028881683315482391326080467539545 + d *
    (-150514995650136489584515603377872680 + d * (50880397388855386972911372725985597 + d *
    (-16449411644944011615377498964081724 + d * (5068263162793194282240379421161446 + d *
    (-1481673528393645365896559754676499 + d * (408640444004008813907002913148998))))))))))) + d
    ^ 12 * (-105526384555612382163643584587255 + d * (25265313843665643008493028457298 + d *
    (-5536371365616103383493141596018 + d * (1091675060448748584665296754717 + d *
    (-189304392731984287095139228396 + d * (27926458482514554756471726316 + d *
    (-3320543359303050676285391674 + d * (285857101775382758503309960 + d *
    (-12952986776844956055719519 + d * (-212228280121297912651452 + d *
    (-18749590367465513908140 + d * (19568184981020951510973))))))))))) + d ^ 12 *
    (933028197821072360032 + d * (-1626686108798904719448 + d * (407158025972802796736 + d *
    (-52372553395212709845 + d * (3000217769997586303 + d * (125267720313153311 + d *
    (-31101198447410527 + d * (1226247295199330 + d * (15019977839843 + d * (10743512602205 + d
    * (-619791015463 + d * (-174883022041))))))))))) + d ^ 12 * (5028521281 + d * (1234168212 +
    d * (58451824 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_13 (d : ℚ) :
    orderSevenSelectionPolynomial d 13 = selectionExpandedAt13 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 13 =
      selectionNumeratorAt13 d := by
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
      selectionNumeratorAt13
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 13 =
      selectionDenominatorAt13 d := by
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
      selectionDenominatorAt13
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt13 selectionDenominatorAt13 selectionExpandedAt13
  ring

private theorem selection_cofactor_eval_at_13 (d : ℚ) :
    (selectionCofactor d).eval 13 = selectionCofactorAt13 d := by
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
    selectionCofactorAt13
  simp
  ring

private theorem selection_factor_at_13 (d : ℚ) :
    selectionExpandedAt13 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 13 *
        selectionCofactorAt13 d := by
  unfold selectionExpandedAt13 orderSevenDualKernelPolynomial selectionCofactorAt13
  ring

theorem selectionEvalAt13 (d : ℚ) :
    Internal.SelectionEvalCertificate d 13 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_13, selection_cofactor_eval_at_13,
    selection_factor_at_13]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 13 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt13 d
#print axioms solution
