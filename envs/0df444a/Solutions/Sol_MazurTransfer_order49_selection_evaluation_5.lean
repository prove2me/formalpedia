-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:37:09.818526+00:00
-- url     : https://prove2.me/submissions/fc8311c9-893e-4f61-b8e5-9e3853b598ed

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval1.At5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 5

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt5 (d : ℚ) : ℚ :=
  -512000000000 + d * (-814848000000 + d * (4161899136000 + d * (-7331812222784 + d *
    (-3803965627776 + d * (58042214162304 + d * (-170209794661440 + d * (269793780273984 + d *
    (-122935658688576 + d * (-714603085844288 + d * (2830132343393472 + d *
    (-6731495579642112))))))))))) + d ^ 12 * (12570538154936384 + d * (-19940136481523904 + d *
    (27835810695494784 + d * (-34860642330944256 + d * (39630122825525376 + d *
    (-41189273494778496 + d * (39296706088550656 + d * (-34489439804299584 + d *
    (27868709950750848 + d * (-20708550269605248 + d * (14104591400360640 + d *
    (-8766286632996288))))))))))) + d ^ 12 * (4947112816912320 + d * (-2517772445593920 + d *
    (1144474051628736 + d * (-461654910067136 + d * (168178503351744 + d * (-59168141057856 + d
    * (21700575460032 + d * (-7968215944896 + d * (2544102883008 + d * (-653815108416 + d *
    (160008792768 + d * (-52384819776))))))))))) + d ^ 12 * (17802554304 + d * (-3962861376 + d
    * (474889536 + d * (-91720384 + d * (47121984 + d * (-10624704 + d * (326592 + d * (122496 +
    d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt5 (d : ℚ) : ℚ :=
  -606375000000 + d * (-1109938200000 + d * (6608003696000 + d * (-15718108936320 + d *
    (15447014791104 + d * (35108976874432 + d * (-186000516591872 + d * (430972593450496 + d *
    (-646741639565824 + d * (519181873598272 + d * (453164300793344 + d *
    (-2791924630136448))))))))))) + d ^ 12 * (6797355353229120 + d * (-12302185206046016 + d *
    (18530442781616384 + d * (-24260223342037248 + d * (28280222755835968 + d *
    (-29869907924192128 + d * (29045343049762688 + d * (-26440226651545344 + d *
    (22899725763395328 + d * (-19091475701689472 + d * (15380514227105024 + d *
    (-11929849504804608))))))))))) + d ^ 12 * (8839943050042560 + d * (-6207509282126272 + d *
    (4104266519723648 + d * (-2540736837331328 + d * (1463188131100480 + d * (-778177442718656 +
    d * (379575768340224 + d * (-168696887442944 + d * (67644773580096 + d * (-24021313461632 +
    d * (7321844624768 + d * (-1828906690560))))))))))) + d ^ 12 * (348783960064 + d *
    (-44055036416 + d * (2010765312 + d * (367742976 + d * (-54353920 + d * (-1355776 + d *
    (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt5 (d : ℚ) : ℚ :=
  26803636208984375000000000000000000 + d * (-867905751833000000000000000000000000 + d *
    (-8940062626166123460000000000000000000 + d * (32870721126277463471168000000000000000 + d *
    (101877677795436593119679680000000000000 + d * (-942726847974268594848335987200000000000 + d
    * (2221928642714171658739113246412800000000 + d * (3353787203629025618285080363869798400000
    + d * (-39723247061369829810124352312737628160000 + d *
    (126391246740595851669753949851157614034944 + d *
    (-128692097031209913468255555067555906846720 + d *
    (-612172151254100368436825229302813970661376))))))))))) + d ^ 12 *
    (3546309997992812173837149255192996137140224 + d *
    (-9464163964738744587277686302364596112195584 + d *
    (11831293126414622231042303996852248146083840 + d *
    (18009056644038651461745433117298281090646016 + d *
    (-145848313755391052356957723800540591788392448 + d *
    (450588732139781600257772735925978306770108416 + d *
    (-871254342606047358036974170881443868217180160 + d *
    (807147531656179660599754558628893910296428544 + d *
    (1535435191634665008504239852132217583860449280 + d *
    (-9618783491080155674420545720756572616640954368 + d *
    (27530015127869454417795287752299144661248507904 + d *
    (-54864637999508510874641563882859919506342674432))))))))))) + d ^ 12 *
    (74362710835217463154645678324302051283948273664 + d *
    (-30996508826817608728120637246752091548414902272 + d *
    (-191763488362868403618728174333471970915853271040 + d *
    (778465487931495303987503804977378330814242095104 + d *
    (-1930152382479195119085946864455175076897046659072 + d *
    (3693262996929015417443992488866629480384154566656 + d *
    (-5600483949277716366153419647390216950921321250816 + d *
    (6080483043457311837885382234338937111703429316608 + d *
    (-1667260909479307188240112074927137849865277014016 + d *
    (-13835918547812339096228214746944130596754995019776 + d *
    (49931569747580439922032280971426842849215766593536 + d *
    (-119308886756579680000893913494443606704893368729600))))))))))) + d ^ 12 *
    (236566685108009478903668946810502536468021864038400 + d *
    (-415445172263160490386269355290655117814702809808896 + d *
    (664551882824877630688104892555900337344403813171200 + d *
    (-982034288707178987201004602457766962695674399031296 + d *
    (1350156115152311197236972748298930761666604180701184 + d *
    (-1731117006862445376927393048631837050335851610636288 + d *
    (2065558572335543832550485644483360805434706539315200 + d *
    (-2274927096831960930418049193751797804428735362629632 + d *
    (2268221349896881649916462084051739708347058487820288 + d *
    (-1952763242994991260674819031228202063424800101498880 + d *
    (1247693520125861960084359164153633361139111656423424 + d *
    (-98143654904981614849487893699175610901864723775488))))))))))) + d ^ 12 *
    (-1512341236610325416404875227366259375688699199881216 + d *
    (3553454713487331073136901946508003675307101956603904 + d *
    (-5945618770201748027452551949302777519418417411260416 + d *
    (8564156031369174546832298603131837499156531294502912 + d *
    (-11249900040068775653146931944376734364028902231244800 + d *
    (13824944213160074097112062126223751801614660005265408 + d *
    (-16111397531333014369620514460879834381441324958613504 + d *
    (17950541843344592386677549455643299618181884979183616 + d *
    (-19219738132896738869465781689033896174722039921770496 + d *
    (19844799650615672699849365627955482762030876282847232 + d *
    (-19806265466455927737234480631516157659890567987593216 + d *
    (19138945927332642977674874091592774389091375660138496))))))))))) + d ^ 12 *
    (-17925117935860179460961781311861400720446744753602560 + d *
    (16282659379560015575977290027763455909241445842157568 + d *
    (-14350079445753791944002990132764924017713244020932608 + d *
    (12270717080193201040036209341906675200235332968906752 + d *
    (-10178300723798281508813178268549940990678807203020800 + d *
    (8185624047186373379027599855710890745729139172704256 + d *
    (-6377402566161177667801411003268025474144745560997888 + d *
    (4807589303982718679313316331831855641553959418855424 + d *
    (-3500705964994408545511971054971474727835356026634240 + d *
    (2456218647274698653755843864736545497966575598436352 + d *
    (-1654722891560863532393886049889457612971774575902720 + d *
    (1064702754194341679347521765981270989795564215074816))))))))))) + d ^ 12 *
    (-648837299257213583324340049011333929556729310478336 + d *
    (369158269480674336275536455858219394206316472303616 + d *
    (-190722973079882977502416282695004760682336915816448 + d *
    (83782180023376400526336056987404382111441895292928 + d *
    (-24648916730002754108423123131908211179946736615424 + d *
    (-4403703512135365039718049206120185719291803860992 + d *
    (15858408513486287345695313711205259448114470191104 + d *
    (-17964825940757116921900969486294543343063138041856 + d *
    (15803083752279155713446597369898673752141871185920 + d *
    (-12243922223391188670171258386136564608399720316928 + d *
    (8727154661389332697897286392926194351754773528576 + d *
    (-5839181122285763243427317813490065761158166478848))))))))))) + d ^ 12 *
    (3707490821740576037255310548576000351693717372928 + d *
    (-2248253712439265207438673731472617992957513695232 + d *
    (1307323790985038127926378878327817511480859557888 + d *
    (-730800351914154597523247590822441089418741678080 + d *
    (393359103774135410043730308409957178813636149248 + d *
    (-204065200827619163790063517499333011195867430912 + d *
    (102080685534994886607516557151698020939323932672 + d *
    (-49244145057731386297290997008224352349186162688 + d *
    (22903745143185508977108200181971218207984320512 + d *
    (-10265551827101860319154832076315586013399613440 + d *
    (4430483665593550081111838052402033935154151424 + d *
    (-1839372998310048247239445295317662417335091200))))))))))) + d ^ 12 *
    (733633429828946707507077778334262107369635840 + d *
    (-280669626812472152390577307877198148860903424 + d *
    (102800930787856002593808366915485370879574016 + d *
    (-35967067320851342959882651484017120485572608 + d *
    (11988290050603933211478928142627417329500160 + d *
    (-3794675399016596741827273209466945716879360 + d *
    (1136362629601706558434818654646740967227392 + d *
    (-320496354659064333238125731210976714817536 + d *
    (84669436696595601658973914785824662618112 + d * (-20812711274212417680880545451701166407680
    + d * (4720561634703398425136490834521326354432 + d *
    (-977243631876443021529477022833279238144))))))))))) + d ^ 12 *
    (181935996071831414401495893785735593984 + d * (-29805997402438317101195407151582674944 + d
    * (4147029919345935011883816992172933120 + d * (-457155266391799065770205157683888128 + d *
    (32867410834816008481793696767934464 + d * (30496363265282741811606747873280 + d *
    (-388775312047365467844909412384768 + d * (51765147575034819775804867608576 + d *
    (-2859706531279892719486047617024 + d * (379028200082654714450478628864 + d *
    (-220557340785915683846055526400 + d * (62160977182272810732855754752))))))))))) + d ^ 12 *
    (-9537147196988831642132414464 + d * (670797059729182948168826880 + d *
    (40170210240735903110135808 + d * (-14707262150158566407012352 + d *
    (1358743829482155678629888 + d * (-11490255039828452966400 + d * (-6825207569812687683584 +
    d * (219600899788827525120 + d * (12055018317879967744 + d * (4566878527875973120 + d *
    (-326471838964121600 + d * (-56254995108462592))))))))))) + d ^ 12 * (1585428396244992 + d *
    (344904265629696 + d * (16128639500288 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt5 (d : ℚ) : ℚ :=
  81084661185741424560546875 + d * (-2575056494295597076416015625 + d *
    (-28743749363791408538818359375 + d * (84635471913323796417236328125 + d *
    (393383330728373453715820312500 + d * (-2726142029301647730037060546875 + d *
    (4593969581765097143159678515625 + d * (16582105483381277482657179631250 + d *
    (-116850412212838183436695605615000 + d * (290034837903964232106562915601416 + d *
    (-50318978559952694911866283010620 + d * (-2300629126824844005116957767676329))))))))))) + d
    ^ 12 * (9417165341991737666752440715910472 + d * (-19559124038071579738780052807026006 + d *
    (10099115567971034217911572984024653 + d * (88776266457579724577309239274063306 + d *
    (-397743559887898983922183382786683888 + d * (974533004613265068983269253435652718 + d *
    (-1425966340168429528272067383103692883 + d * (143631298780923331708241955212785833 + d *
    (6556171461385637538573823128655379013 + d * (-24181959910477970847358415170467850389 + d *
    (56087303393316142332923962936512910883 + d *
    (-91994898876557103619462594982394528436))))))))))) + d ^ 12 *
    (86178432636496089469104875610044942030 + d * (71830653839848340883676184372353220346 + d *
    (-578074823865290152153198171938406330355 + d * (1689901790034008203702436520298418119483 +
    d * (-3596156588551454146768764677588150124159 + d *
    (6105250435280764102251883464826808088829 + d * (-8081468124175102079294690588618096793374 +
    d * (6604523909757949566323617922453601985035 + d *
    (4084952291112718212369498426599276000121 + d * (-33672559915937747499897915916227395595375
    + d * (96590500584911281244909285349792746144596 + d *
    (-212200152435516342984868969706859682450616))))))))))) + d ^ 12 *
    (403984699923368807982774148555712492151206 + d *
    (-697532969759688222957350004104702361726048 + d *
    (1117332550092977366496322602339073737845693 + d *
    (-1682682739003141234960932937436154328397530 + d *
    (2403312331249038122176626505569987820477981 + d *
    (-3275466987790660818504252551875350405544991 + d *
    (4279260066065921738338515851677126327472783 + d *
    (-5377940967826076551773444673568239443182313 + d *
    (6519449600147342684131210631228317777949154 + d *
    (-7640251389798746490766451078379276871128681 + d *
    (8671059263945507132469433043649864980683285 + d *
    (-9543721981592929822631782603164218763537869))))))))))) + d ^ 12 *
    (10198351691139907053973649361752641438391814 + d *
    (-10589711456230786640288294678272401962703845 + d *
    (10691989842106815896972180709209355731501575 + d *
    (-10501330962644838095983860838466904083361566 + d *
    (10035820511863154478728181116298985416138097 + d *
    (-9332995933795434775609657614014409339169213 + d *
    (8445294760641363176439897435449652717164956 + d *
    (-7434127548329999182999436796479341844298560 + d *
    (6363420598671202830183990576646147586092698 + d *
    (-5293495756039125951750446566806134795109395 + d *
    (4276039249784521143911884185173455142843218 + d *
    (-3350683029594300143569696609858639118042795))))))))))) + d ^ 12 *
    (2543426835464880921148186802144549696640561 + d *
    (-1866826783704974663167200448886221669781298 + d *
    (1321624531432768131204834839539037038534805 + d *
    (-899332188465188523867132301293488288503639 + d *
    (585238897428578558159980702281740460393161 + d *
    (-361355785947971974953471469040745007177220 + d *
    (208937291369441249867268374510261378484501 + d *
    (-110370162226659452382209858266591325556059 + d *
    (50370319901167050152200738423024634493420 + d * (-16545789706619594515264167616772627781419
    + d * (-541966246406745286548845785040430903923 + d *
    (7656252157605154644347053114376034353925))))))))))) + d ^ 12 *
    (-9346990644528604309330368919619093221146 + d * (8469543708436140162352658245094547496148 +
    d * (-6672950725860405049094580094393774706617 + d *
    (4808576946449799457367310105945809729483 + d * (-3241523187283157512745378454017668040580 +
    d * (2068580569010732996265060626142539893489 + d *
    (-1258272682485114806406365919748557644980 + d * (732625733688729847867895757431116901674 +
    d * (-409384228972108751112276218319551798569 + d * (219893863047826363821351884842813061791
    + d * (-113634519207852407106709962962703784507 + d *
    (56516291838707671207936886825379586816))))))))))) + d ^ 12 *
    (-27050119248670388715214465057296343172 + d * (12453854541316826890772727218254087811 + d *
    (-5511099742589840241180753126703196470 + d * (2341479858714914783018353518509106351 + d *
    (-953740540601465792226598987334138052 + d * (371764331413909864034791366355364729 + d *
    (-138367059191550242136523263512072136 + d * (49039396549374266761433558314204541 + d *
    (-16495779101947391786689743750443548 + d * (5245351033912808469522654614578398 + d *
    (-1569005629982846519816709553875235 + d * (438848702065197178768013224854742))))))))))) + d
    ^ 12 * (-113927091668589587190284434382943 + d * (27198932754657755421649145607898 + d *
    (-5902190190725337365051263854962 + d * (1146573620918779544233962716237 + d *
    (-195308266945272697064112095276 + d * (28305755680292460091580024068 + d *
    (-3325751292879297867065866698 + d * (289926275360121241140424592 + d *
    (-15446234983151169877060863 + d * (394752291795364647354044 + d * (-99561470338575588840436
    + d * (23890478132703777725501))))))))))) + d ^ 12 * (1412658502158523791608 + d *
    (-1737147215677754018376 + d * (413889193699221181824 + d * (-52157262586968883757 + d *
    (2980917150316598367 + d * (121119152537684583 + d * (-31125182723814831 + d *
    (1298940987828346 + d * (15827302469091 + d * (10261930698069 + d * (-651953749455 + d *
    (-176092526057))))))))))) + d ^ 12 * (4992945457 + d * (1233761812 + d * (58451608 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_5 (d : ℚ) :
    orderSevenSelectionPolynomial d 5 = selectionExpandedAt5 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 5 =
      selectionNumeratorAt5 d := by
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
      selectionNumeratorAt5
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 5 =
      selectionDenominatorAt5 d := by
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
      selectionDenominatorAt5
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt5 selectionDenominatorAt5 selectionExpandedAt5
  ring

private theorem selection_cofactor_eval_at_5 (d : ℚ) :
    (selectionCofactor d).eval 5 = selectionCofactorAt5 d := by
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
    selectionCofactorAt5
  simp
  ring

private theorem selection_factor_at_5 (d : ℚ) :
    selectionExpandedAt5 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 5 *
        selectionCofactorAt5 d := by
  unfold selectionExpandedAt5 orderSevenDualKernelPolynomial selectionCofactorAt5
  ring

theorem selectionEvalAt5 (d : ℚ) :
    Internal.SelectionEvalCertificate d 5 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_5, selection_cofactor_eval_at_5,
    selection_factor_at_5]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 5 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt5 d
#print axioms solution
