-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_8
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:59:34.094955+00:00
-- url     : https://prove2.me/submissions/ed872544-08ac-43a5-a131-ebbd2165e526

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval1.At8. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 8

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt8 (d : ℚ) : ℚ :=
  -134217728000000 + d * (-95661588480000 + d * (404399847014400 + d * (-844361939937344 + d *
    (757799806429056 + d * (1054393943815680 + d * (-4974942318436032 + d * (9428470346824320 +
    d * (-11210490312422400 + d * (6044363500906048 + d * (9601472880028992 + d *
    (-35882160942924864))))))))))) + d ^ 12 * (69240956228820416 + d * (-103707872769194304 + d
    * (132401626957829376 + d * (-149581024104340032 + d * (152590923254730624 + d *
    (-142199793928748352 + d * (121786092971423104 + d * (-96206458943132544 + d *
    (70290432038263872 + d * (-47507941996380096 + d * (29606856770807040 + d *
    (-16941320327809536))))))))))) + d ^ 12 * (8879104518066240 + d * (-4248220189454784 + d *
    (1836921206392704 + d * (-708456251413184 + d * (246018174898176 + d * (-82454105757504 + d
    * (29225687748288 + d * (-10486743601920 + d * (3233526908544 + d * (-782896482048 + d *
    (180845536896 + d * (-59447717376))))))))))) + d ^ 12 * (20181006336 + d * (-4288820928 + d
    * (455487552 + d * (-85271488 + d * (47550528 + d * (-10617792 + d * (326592 + d * (122496 +
    d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt8 (d : ℚ) : ℚ :=
  -159025459101696 + d * (-127178580688896 + d * (617026564653056 + d * (-1491525828157440 + d *
    (2127135784359936 + d * (-854608268389376 + d * (-3539698592417792 + d * (10152967701176320
    + d * (-16891514875689472 + d * (20181539821646848 + d * (-15565442278928512 + d *
    (979466566916160))))))))))) + d ^ 12 * (22293571348632192 + d * (-50159302575602816 + d *
    (76151947161234176 + d * (-93813621030336960 + d * (99864692335479232 + d *
    (-94998583573480000 + d * (82654843380544064 + d * (-67203520475283264 + d *
    (52114391573013504 + d * (-39070241519935424 + d * (28412922559895168 + d *
    (-19973957432462976))))))))))) + d ^ 12 * (13494380446019520 + d * (-8707099618315456 + d *
    (5335187639417984 + d * (-3087987385192064 + d * (1677387989482432 + d * (-848240271616064 +
    d * (396404453979840 + d * (-170313072219968 + d * (66804475524672 + d * (-23514910300544 +
    d * (7183742838656 + d * (-1809734123520))))))))))) + d ^ 12 * (348421367296 + d *
    (-44265978368 + d * (2006074368 + d * (371914752 + d * (-53933056 + d * (-1352704 + d *
    (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt8 (d : ℚ) : ℚ :=
  492703368427931840545834528979686875201536 + d *
    (-20419506342029022795381603756393786729562112 + d *
    (-55527119627035242341794802273585884538339328 + d *
    (312171356933008009279742993889381752212815872 + d *
    (-319928018200885796780585794453920705041924096 + d *
    (-1531027893321358618378219280788963245112164352 + d *
    (7504988857327497186654550445932560870027558912 + d *
    (-14087043918854334432431081518985515339373084672 + d *
    (-489290149162893024062965941710293782201630720 + d *
    (79342686714750909286559158931406434067821101056 + d *
    (-246377297911840409009849990505658874243337945088 + d *
    (385951653548162847019400952863728135034171293696))))))))))) + d ^ 12 *
    (-75942323989626873419499736907380917462951788544 + d *
    (-1425573484278039414807043783657746984030713937920 + d *
    (4672693101387147994450600492515534025697139359744 + d *
    (-8689119860247995414154879271728541787053552828416 + d *
    (9037466348435450310964854478940704720118571335680 + d *
    (3278578359425584474904019674291993301944759222272 + d *
    (-39374515430471492968221358992456092591532318654464 + d *
    (103635542267698763373419180191733101707696239017984 + d *
    (-178018665844563046618826217877468917260609645445120 + d *
    (204818578286176507360283538194639562108177415405568 + d *
    (-80801124991962329532302788352672061655968312197120 + d *
    (-319357861131943637259156385792315558722497773305856))))))))))) + d ^ 12 *
    (1075990240791858762994416438517336206584247529766912 + d *
    (-2116095117079603324370522632869183639119974790070272 + d *
    (3094683485192958291766643219187838549099315295158272 + d *
    (-3327228853170208899677440083252904342899313643880448 + d *
    (1850011022860711488675296034387241864876912971612160 + d *
    (2331805273998242634172377781397419132311721726967808 + d *
    (-9805137923182432075744179051300236612932897650245632 + d *
    (20201364438292817139986685714963285102548073036382208 + d *
    (-31707207841895488562952910028468657857008399449325568 + d *
    (40845564851921187851231053200156481374618027331420160 + d *
    (-42709485915479976700502484067664333361293411289661440 + d *
    (31724267769148557655006240529123108649358909272752128))))))))))) + d ^ 12 *
    (-2850083228821510643375166555928951090778566396477440 + d *
    (-47026279980242277055333013628731297215314703278145536 + d *
    (117866412349137721659308053389274962995880014763261952 + d *
    (-205778980794457461657922381611699473022949716179550208 + d *
    (303088677379729105728089063814643181316932955637022720 + d *
    (-399231378352882571677466569489728130662966081661435904 + d *
    (482319793221748680678421965709672102615485958116081664 + d *
    (-541055431899598482377220779638336013725632132079419392 + d *
    (566584338855669792688502005390248911417746027338006528 + d *
    (-553921165793047737361142290036880168771291877551374336 + d *
    (502681745716932497338956241647348394895457774791819264 + d *
    (-417028907961064579349826841932663657592917377796800512))))))))))) + d ^ 12 *
    (304903249618183930186493495157758762324620591559081984 + d *
    (-176740571409690229886353634127479396665889535629197312 + d *
    (43947473799665893574584880547534381189402219260674048 + d *
    (82588473139000281704824936399730381701604460130467840 + d *
    (-193726593859922377752407084864413711397603889381638144 + d *
    (282894084461071245345198533625776393431160397585448960 + d *
    (-346447884034470997353718077680873812078519115035967488 + d *
    (383608040063752983958478800938113408853471308390072320 + d *
    (-396052819614351902260876725879920262587341620671938560 + d *
    (387297059972402590735167654817389459707253716955168768 + d *
    (-361979838587683780438964344562286079573611556522164224 + d *
    (325171768662504457412463969150065872080621984466337792))))))))))) + d ^ 12 *
    (-281784148943697850685485831448247730868557052123283456 + d *
    (236129427606396103147439249179668517902611367123222528 + d *
    (-191650942696735690544979359304183118483188577353072640 + d *
    (150813665787066178128854171647500954175402133242511360 + d *
    (-115128903345698601399161619313041506580863675956723712 + d *
    (85275333887234547989280416406050959567679618497642496 + d *
    (-61275918524660884439315266728160451811625023728779264 + d *
    (42693719813397165267477200411504151524354893917192192 + d *
    (-28817471942303224902970358116348188780654161047584768 + d *
    (18817604049124608944995605262847661822692014817017856 + d *
    (-11863252860774943864475369971307547235841630227660800 + d *
    (7199058541946796748033065769995097357570141227319296))))))))))) + d ^ 12 *
    (-4186359804088119969378765380674602151996391386775552 + d *
    (2316611091094320858645252581246734463273283991633920 + d *
    (-1205776444387111703450229906169426036953210263437312 + d *
    (577745601887447371633879437047344721049160143601664 + d *
    (-243175843508804579441984267354639066545870798848000 + d *
    (78206382330780855667784572543067859080455033454592 + d *
    (-5662145969900927030746958923697139124762571702272 + d *
    (-20093087010368932484373151641401259722712233541632 + d *
    (24497365067657567587157701411601468669791361826816 + d *
    (-20750521287497382700410023881016623686325927936000 + d *
    (15072833597676711655054582702258023004238330986496 + d *
    (-9976267168520856743904124398839979904375120199680))))))))))) + d ^ 12 *
    (6174561883066651764647443885588797554281901457408 + d *
    (-3621691192562779565462997496882080090396799270912 + d *
    (2028679306339247027880556296931501741765219319808 + d *
    (-1090299265434944395094142783907452759696231628800 + d *
    (563880714767892272204462559952250030890513858560 + d *
    (-281150264340429585666796572649813307758296694784 + d *
    (135292545568060530581087578388522890541668499456 + d *
    (-62868023805497878048722480948358499090092261376 + d *
    (28213529212335530983498259577644244243499188224 + d *
    (-12225134968213317437723350335018120847993077760 + d *
    (5111859534345386425488232830821970688650248192 + d *
    (-2060937952840525334636488909312126774061563904))))))))))) + d ^ 12 *
    (800231454979901903104595274208885092587143168 + d *
    (-298814472088632710170816951981807884582518784 + d *
    (107114499281990755247950166158446296194088960 + d *
    (-36780385512440907260628258568849729936949248 + d *
    (12066301350880891734074408150956795210498048 + d *
    (-3770169533087398187536187464074181575966720 + d *
    (1117730874503528629365401224048145027563520 + d *
    (-312984240903930579970522328482887849738240 + d *
    (82320355480692409670038718523193159319552 + d * (-20198823219778028749429491057381225267200
    + d * (4584106967221362330516542526914877718528 + d *
    (-951622561387776992635374972130775007232))))))))))) + d ^ 12 *
    (177986593976948852889892112289139523584 + d * (-29337482664836546614469463875039526912 + d
    * (4110677879668492496537659863741235200 + d * (-456222172037322351915586464588234752 + d *
    (32824048080548040589848471091019776 + d * (127544660949697441108767606833152 + d *
    (-421077294144560375432594781896704 + d * (57118871364252343923037160079360 + d *
    (-3235608472783846934094969307136 + d * (338973726633678615279560556544 + d *
    (-206702117194684318022663929856 + d * (60624641628445369448792064000))))))))))) + d ^ 12 *
    (-9503920553473697360061399040 + d * (681497146096485318891405312 + d *
    (39226424898877484088950784 + d * (-14731181797824343454515200 + d *
    (1360661279518431524421632 + d * (-10683657797942140993536 + d * (-6836786293071374188544 +
    d * (209206073656310759424 + d * (11991938772119584768 + d * (4624574802465390592 + d *
    (-322818626556526592 + d * (-56116738588672000))))))))))) + d ^ 12 * (1589384208973824 + d *
    (344947236274176 + d * (16128655228928 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt8 (d : ℚ) : ℚ :=
  414263652701401487106913926643712 + d * (-17008785398384462258763233732067328 + d *
    (-53558088219369365174573594893615104 + d * (254574638129547000690510368281198592 + d *
    (-138361954890844023640340382672224256 + d * (-1556501285906773609652666086453149696 + d *
    (5923588147476817328741442928781557760 + d * (-8380421100299049679442627729355440128 + d *
    (-8969345879411387230366464740339363328 + d * (71999411878848481030107743943410309737 + d *
    (-174039210772225277020805554971668514934 + d *
    (192514935718858847455979776502781926993))))))))))) + d ^ 12 *
    (180355875790286887955535316810948921635 + d * (-1333252881965632434032869251553149271954 +
    d * (3266388350248582587220501557995946688875 + d *
    (-4741296112890485067591107362203808760038 + d * (2492062874912726893992422515440350961542 +
    d * (8445083821193300362152551926900729499668 + d *
    (-31943371488266203061181214344046676649652 + d * (64917718420698309586377808908366125895276
    + d * (-89843628942427221640003719154814879037948 + d *
    (70146600786925532569362467195258857983009 + d * (44668814313682575185727779761477595196200
    + d * (-297886372620734915615578919234277369076312))))))))))) + d ^ 12 *
    (687593941670744010142555570534419862583633 + d *
    (-1120921448142042828671326578394622874413490 + d *
    (1380685872215526866702764245979231490954197 + d *
    (-1131116044344560051206868572757842468606202 + d *
    (-14696183636335340105430393488611740547113 + d *
    (2359984226633623369842024223997830708504975 + d *
    (-5943074142042750446157147762965035085672669 + d *
    (10357613156309145633478998495710775219285336 + d *
    (-14637639250926468371739054445167038543667441 + d *
    (17265729379252342273906930411399160784291489 + d *
    (-16334894625771588519612279662658133466267672 + d *
    (9852160915490321061813324982886128168072921))))))))))) + d ^ 12 *
    (3872214617918423285095156242504639831755636 + d *
    (-25836066088891633254318558184369410466353099 + d *
    (56049287604141711960624564270916083644660780 + d *
    (-93402586778034520117541806436587286949223195 + d *
    (135734220137266637643385390947073231537996414 + d *
    (-180082269477346842076089814895262976198016273 + d *
    (223070556763763146486277798064619838530835279 + d *
    (-261352341968129363016111165046022495868803223 + d *
    (292031182912136498024833223973622702778010285 + d *
    (-312990959870043891058216267601309030803928613 + d *
    (323091504803118327514640944735445493777279397 + d *
    (-322215381499204385037492658434157495890677021))))))))))) + d ^ 12 *
    (311178407030205971238735889137412565181911487 + d *
    (-291536550472358717958958744346622127776423089 + d *
    (265332421834165032524050083575119950037163554 + d *
    (-234825673693757827092656960517902508764884715 + d *
    (202245211544298664988345985712848764973939259 + d *
    (-169590117865844018688187268668027455511641604 + d *
    (138493701272163858896804114451291864459103123 + d *
    (-110153526372314221759627431772946012878016192 + d *
    (85321170009393546625489701489961260296139465 + d *
    (-64339410481794098146113732025137638364909506 + d *
    (47211575078934672265813426318001487636816631 + d *
    (-33687456423181017043332062868514203630648431))))))))))) + d ^ 12 *
    (23351967982352044816152499139225072578181508 + d *
    (-15705848350086302827974600981294230445692139 + d *
    (10231512740914159341246306557239279509178124 + d *
    (-6440906634136563511430968863640147451821519 + d *
    (3905398242529721528428007241333732897309338 + d *
    (-2270021109078389918140467775106828358551093 + d *
    (1255644948953203369648285162849901779370661 + d *
    (-653010475410563755005910207810243431519599 + d *
    (312240328845046339563072931984452141858057 + d *
    (-130709600084072890786685235344484833752250 + d *
    (41281914304589177026334165407324924914337 + d *
    (-2083901411948346245180499758094276530412))))))))))) + d ^ 12 *
    (-11682658266934797558706555779447971248782 + d * (13862027761936366551833903539517590288871
    + d * (-11646028113849562287205477499060389178791 + d *
    (8423277426633079646213297370734189342714 + d * (-5557485586970703204412288699322551919046 +
    d * (3429381700376918964175471244280956503153 + d *
    (-2004936378864982863846597703789149840172 + d * (1118775705697812086622012214079533743514 +
    d * (-598531824514687189581809942104024779196 + d * (307845648701842946564509951028794228387
    + d * (-152476320434632966580871940637493069811 + d *
    (72792374067659380894741552129203177205))))))))))) + d ^ 12 *
    (-33506269586164251382525080330073578584 + d * (14868470389788579079689669714880259846 + d *
    (-6357367518323779238224930083655521598 + d * (2616792282972094379423224893329583156 + d *
    (-1035599984211179837805003117979192266 + d * (393393327940266967648274043445519245 + d *
    (-143142921113168316238180133892544560 + d * (49762659649817613188572396132446692 + d *
    (-16476145929162627348054375481497649 + d * (5175285180532182558950667661233876 + d *
    (-1534753500152507955184461809941309 + d * (427110947016466865187997665857383))))))))))) + d
    ^ 12 * (-110697438170755630475954068460730 + d * (26464317919928538409726478142583 + d *
    (-5765032266209090252099971800938 + d * (1126305658889633234445285049382 + d *
    (-193137661181507590620043150646 + d * (28174101204788028848106731251 + d *
    (-3324190939031675951815958514 + d * (288265031392511570918430620 + d *
    (-14482090298533140020550429 + d * (164881390043549911075403 + d * (-69318469715644173491275
    + d * (22290778066828570306733))))))))))) + d ^ 12 * (1232944566561040184867 + d *
    (-1695909790181637857598 + d * (411352869467949043686 + d * (-52235251576982279465 + d *
    (2988309539813341338 + d * (122657794792647186 + d * (-31117964621746152 + d *
    (1271602732803760 + d * (15522230034768 + d * (10442492815305 + d * (-639892791453 + d *
    (-175638962051))))))))))) + d ^ 12 * (5006286391 + d * (1233914212 + d * (58451689 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_8 (d : ℚ) :
    orderSevenSelectionPolynomial d 8 = selectionExpandedAt8 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 8 =
      selectionNumeratorAt8 d := by
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
      selectionNumeratorAt8
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 8 =
      selectionDenominatorAt8 d := by
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
      selectionDenominatorAt8
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt8 selectionDenominatorAt8 selectionExpandedAt8
  ring

private theorem selection_cofactor_eval_at_8 (d : ℚ) :
    (selectionCofactor d).eval 8 = selectionCofactorAt8 d := by
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
    selectionCofactorAt8
  simp
  ring

private theorem selection_factor_at_8 (d : ℚ) :
    selectionExpandedAt8 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 8 *
        selectionCofactorAt8 d := by
  unfold selectionExpandedAt8 orderSevenDualKernelPolynomial selectionCofactorAt8
  ring

theorem selectionEvalAt8 (d : ℚ) :
    Internal.SelectionEvalCertificate d 8 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_8, selection_cofactor_eval_at_8,
    selection_factor_at_8]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 8 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt8 d
#print axioms solution
