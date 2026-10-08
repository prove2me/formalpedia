-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_35
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:10:09.289811+00:00
-- url     : https://prove2.me/submissions/31812a79-4766-4a5f-a2e6-bfd4791c275e

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval7.At35. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 35

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt35 (d : ℚ) : ℚ :=
  -6007723949339000000000 + d * (-487469345229132000000 + d * (514144229625305328000 + d *
    (-1149941759902248893504 + d * (2258023843249287504384 + d * (-1517477675106714692736 + d *
    (312134811300849754560 + d * (181824330200279375424 + d * (-329571754483836845376 + d *
    (417108867200887928512 + d * (-310494117527955728448 + d * (166976529614496718848)))))))))))
    + d ^ 12 * (-81987434482780712896 + d * (30057158986257619776 + d * (5727170480641812864 + d
    * (-19354038918724317696 + d * (18532861113115982976 + d * (-14143016950115316096 + d *
    (9604048882702354816 + d * (-5713539196604130624 + d * (3071664128368662528 + d *
    (-1583567468341623168 + d * (770125390630334400 + d * (-333649369475717568))))))))))) + d ^
    12 * (129945728663229120 + d * (-49670646651063360 + d * (19006032284202816 + d *
    (-6434069447627456 + d * (1730387281080384 + d * (-408973647994176 + d * (125171157239232 +
    d * (-45920726356416 + d * (12615884077248 + d * (-2068311567936 + d * (284205077568 + d *
    (-113485240896))))))))))) + d ^ 12 * (42801996864 + d * (-7195396416 + d * (280869696 + d *
    (-27231424 + d * (51407424 + d * (-10555584 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt35 (d : ℚ) : ℚ :=
  -7120146789307125000000 + d * (-607159236553703400000 + d * (837302903114729408000 + d *
    (-1920204790248073808640 + d * (3540422063737287200064 + d * (-2774191981101687161408 + d *
    (1193347097544439404928 + d * (-446506093655459003264 + d * (117842081519070267776 + d *
    (232070874454675348672 + d * (-315809671226607400576 + d * (236026549664067866112)))))))))))
    + d ^ 12 * (-154733717505679383360 + d * (89899000755323280064 + d * (-33731953370489835136
    + d * (3781277118680867712 + d * (3940928491717960768 + d * (-4305713124797619328 + d *
    (3420514252396350848 + d * (-2178790595223677184 + d * (1180453613638699008 + d *
    (-649685387741988992 + d * (362518675739446784 + d * (-180529528945317888))))))))))) + d ^
    12 * (81041294360612160 + d * (-37430627437851712 + d * (17997438010204928 + d *
    (-8066083503362048 + d * (3294101827856320 + d * (-1314274142710976 + d * (519896293405824 +
    d * (-189737479105664 + d * (62003113455936 + d * (-19221300897152 + d * (5895187242368 + d
    * (-1630670330880))))))))))) + d ^ 12 * (346212250624 + d * (-46150355456 + d * (1963855872
    + d * (409460736 + d * (-50145280 + d * (-1325056 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt35 (d : ℚ) : ℚ :=
  44769051872583332887572850713755562295501953125000000000000000000 + d *
    (-2088348727180056856971352698825286159221723125000000000000000000000 + d *
    (1356399830412216661476579455065253021621708940720000000000000000000 + d *
    (1416722031276382279215255763840790764403859051573104000000000000000 + d *
    (-2343914067546936692314468274568508996671937828388555840000000000000 + d *
    (4055756448479407830340741721684878826067934969753503219200000000000 + d *
    (-3522422073741898067652715499885679341808514295396091316531200000000 + d *
    (142945619802298067075952283620048551832215614417866399730892800000 + d *
    (2837248583979262844794129293778400231478863780664832801029980160000 + d *
    (-4358537376337018225054312980586552606648892255329493477929221881856 + d *
    (4389312427659296320308130780072344961021792700911095862651380039680 + d *
    (-2590275747982396286148730260099795084127547565303784831110005129216))))))))))) + d ^ 12 *
    (-36086550388527695179688128909251930800731044704922703320693866496 + d *
    (2000089483992358998909136964249170997689008114775446428755998539776 + d *
    (-2844770372709305582381709806078425353866836834656890186031518187520 + d *
    (2620648950241944735654080892505431446440040691262875721014193422336 + d *
    (-1584376239656961339184860339152284011330248630951621624819087310848 + d *
    (309289892758392825759487222959645826499728750230769321357090226176 + d *
    (685756011082279631277497340408647703164079538057520775060804075520 + d *
    (-1206031299720147465872847054776910359024817678800601353568414334976 + d *
    (1267059691338661764055102069008847522966467759518241786397780869120 + d *
    (-996519572950660287825600541456272677783460618536991647303154270208 + d *
    (587628175021079215088819831823837588605023067694047818671626911744 + d *
    (-205254279346947392174846751305104402770617577026393714541868613632))))))))))) + d ^ 12 *
    (-66371120964688513671115584226282978706263041524907879042154233856 + d *
    (207922263011930855904146495334036735698302979832121351655213498368 + d *
    (-240300866184392139252318012911433495636292591630777521560652349440 + d *
    (204816782356386816351223174597611715282509316979900639214485110784 + d *
    (-142064846084142015137411382364279774015639557739712060856192991232 + d *
    (79685068917709553873063118738200264374196591524568348833231405056 + d *
    (-31672885111168394760247487436442040549148701679572636559193931776 + d *
    (1772554082351310897880394955161603688371062311679413377477378048 + d *
    (12616678141645005020078577344022920705704166006272802676748058624 + d *
    (-16538071015620320843229579909729918083543932201166168944447062016 + d *
    (14788373951273678531702719470405070009167863814357819811086729216 + d *
    (-10866118944380256511656455371923209202913665852983995891656949760))))))))))) + d ^ 12 *
    (6857634986819903280005809527416059950907169162495184681810001920 + d *
    (-3700229140350041677997830883528770320285584538980416348483485696 + d *
    (1595886472695990383730781221219798336335618356184419091289210880 + d *
    (-390839629846631880859621242590536200893014226248500387640508416 + d *
    (-180501798728251747767844535171375445297395087104505831472234496 + d *
    (370341453370948304750304721858298646813466089020444457467379712 + d *
    (-366701246474909309058267320987627463640513591255197361075650560 + d *
    (287556420352372055553727535119249405588896924434708340475691008 + d *
    (-196115184829734998466476072467615305616303891912897045609316352 + d *
    (119815052262530823862269129959014031880702030543272638891950080 + d *
    (-65851693542958623829289214692110142997584025029435168883736576 + d *
    (31965327569275167692960492540865047963991241877572798617485312))))))))))) + d ^ 12 *
    (-12852755417155060776905980006180606438092574329009181593174016 + d *
    (3279229940253923252065482755151431648010858380459842573697024 + d *
    (786945536625583978337191366539612782797066754414308507254784 + d *
    (-2022259489948382447327498176034189563885592348112940136398848 + d *
    (2003871417325497395337949405491423057906268904595459156213760 + d *
    (-1560708737940523378094863128861279937670454959592102291832832 + d *
    (1072448555758017028893251891523459308054768650415615590793216 + d *
    (-677566987506897427715496458905028220769350753707844799299584 + d *
    (401089197770370450022273791650851101267355669197010251546624 + d *
    (-224531985068249621503534269767391318899418651244927147573248 + d *
    (119352770025993227479047016663958525288321476127840741883904 + d *
    (-60254845291127427254325488330896381140171629618554798342144))))))))))) + d ^ 12 *
    (28778287631914640460180667051653852180509047686598887997440 + d *
    (-12877165277758829345834697485615597451788954155957503393792 + d *
    (5287489069682496279638505281195616689362259574055590428672 + d *
    (-1898273011912006986186176456214206654302230776728066981888 + d *
    (512071016334627352279965750782019205067749326782519050240 + d *
    (-18303128314964086327424674895147707743675248640212598784 + d *
    (-112018523993108822018893602952781522146829281354220044288 + d *
    (114026157027966887357898433226851196350879922890452762624 + d *
    (-83016099035701775643989200732660123254603408484820582400 + d *
    (52288518911409923474103383380687246233826602517964521472 + d *
    (-30164071672024787935185124459471391871879559516728852480 + d *
    (16336161944066146308764695259129210887963809153773469696))))))))))) + d ^ 12 *
    (-8413217179915414316526807192331025712648335028222427136 + d *
    (4150655299389184855759142727647027883618725326032470016 + d *
    (-1970262018571030194644352295831915949762523038430527488 + d *
    (902273318452216760009242406168265775249946270360403968 + d *
    (-399225718107159439839139186921512849410539272140488704 + d *
    (170780792941233233150628322755886776687823216519938048 + d *
    (-70618249745846909131407249491941163618515340514820096 + d *
    (28197411719244624963142645161273368032039436408848384 + d *
    (-10850874124963009376992747223404619733952840598814720 + d *
    (4011149830030627191120881217035827267962278591332352 + d *
    (-1416754030537926251641402524153956697131213040123904 + d *
    (473803511183444577523335254246275878641043625213952))))))))))) + d ^ 12 *
    (-147594472739618694953643062916574450946082280046592 + d *
    (41422824760750448195124807576688125819552710524928 + d *
    (-9616077312007514836390697394327521571621254725632 + d *
    (1259806258914372098854041660277172418767707176960 + d *
    (401361712539831696310640140714239888352439697408 + d *
    (-456310612717118991822573263194735164532251164672 + d *
    (271112866002813691868945496572680460984402051072 + d *
    (-131768890615533124394129173315526070283300241408 + d *
    (57471235536299694912668495259345712096245972992 + d *
    (-23295207035632450761285688607074824059791605760 + d *
    (8923940849280659288491596364558210708941307904 + d *
    (-3260616203622562578470640679562957805580451840))))))))))) + d ^ 12 *
    (1142342553243273099256389330843976882408652800 + d *
    (-384888770717061474800568806295302584783601664 + d *
    (124884421993402899872103653512241534112628736 + d *
    (-39032060686718723967809663735396020906098688 + d *
    (11745142021814279718278644872431244153978880 + d *
    (-3399011776511027891179520828779840536576000 + d *
    (944358238136600587112667553126116653268992 + d *
    (-251191136336851289346394162471352565497856 + d *
    (63706049489139013625005882217088183959552 + d * (-15319131511990974834423960814710279372800
    + d * (3466851246917060893779338634233102467072 + d *
    (-730931362192580417326383370323701530624))))))))))) + d ^ 12 *
    (141464910740221193933309135472380084224 + d * (-24562545596276376649452118255492399104 + d
    * (3680426698454599172514819853729136640 + d * (-440734792650921977962124838049415168 + d *
    (33730000536107493213100685859487744 + d * (554763658650353001207254721495040 + d *
    (-654151197449244542887023250505728 + d * (103367245868765778672486846038016 + d *
    (-7127938448795630755142427213824 + d * (51085262293372974793048981504 + d *
    (-82792523144959698992719462400 + d * (46342848211511346372906319872))))))))))) + d ^ 12 *
    (-9212616600916967778142388224 + d * (783458934736043345191895040 + d *
    (30964391976766895840821248 + d * (-15014530729260212300808192 + d *
    (1375066237518129105993728 + d * (-3073700348000140001280 + d * (-6908313992923693973504 + d
    * (117057672517810913280 + d * (11465131752637333504 + d * (5144361396616560640 + d *
    (-289938725824102400 + d * (-54872429910556672))))))))))) + d ^ 12 * (1624986523533312 + d *
    (345333972074496 + d * (16128796786688 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt35 (d : ℚ) : ℚ :=
  537855385196467086810552023837005026638507843017578125 + d *
    (-25042914829710926223626995232919518041908740997314453125 + d *
    (14038598189223184039968892918590273453550128936767578125 + d *
    (22579047920595914297881912929061433202299559112548828125 + d *
    (-31875757156358226524663820326242708339475142421875000000 + d *
    (44693181690659485478745797129254208013070275915966796875 + d *
    (-29742692168504982622812650365739590078485508242755078125 + d *
    (-14241146030582877700367775131029356763589580497439362500 + d *
    (44463837042757111214436589682402238265464675865957777500 + d *
    (-50042993646308488188175051314926312522846489662018642994 + d *
    (37807265255305159692252868996693898627587345064316800450 + d *
    (-11101080139553850476045368709561452132203413606561234959))))))))))) + d ^ 12 *
    (-16198689113551211395230983677173872928961012687807957488 + d *
    (29621601902146086853823245409344591252923842164813334834 + d *
    (-29065119411385562184095019906865228379632284402208680597 + d *
    (19764247718812722915278657737641013537226599545615887966 + d *
    (-6567333865967474727483010655612370140742504072244030378 + d *
    (-4974883081483540631770750328208945417721137919175586632 + d *
    (11341554864743076560676639680320692033450610240408264457 + d *
    (-12613003128773923064773027082480758771003410592103966847 + d *
    (10394628297908239381961971583579176002150035393828125143 + d *
    (-6479536267743817889639527644303219147900278294570610249 + d *
    (2574833363020786606971283074052655371191611032703213783 + d *
    (253701223558162008255452697861386314806863284812457634))))))))))) + d ^ 12 *
    (-1770393619275793543985070725658440483614332975954023980 + d *
    (2205702519457537435560040841460463602004837075044553536 + d *
    (-1945625341626019490023279504178190430512389167130124365 + d *
    (1383708757841310351667455981093525591023337344609001133 + d *
    (-806646025791651590527041958587935570995241471149232709 + d *
    (355307969512241247390866411395633022573797555822942099 + d *
    (-65670151760241477617592160365461049016310140129286054 + d *
    (-82027440950485258335339450386967811081971448788595755 + d *
    (131041319836615569646055064240064885061321308165352241 + d *
    (-125125830934853953153879106850524108471481775731252585 + d *
    (96350215164831888945273683779074004797289692050692936 + d *
    (-63827348156436747212297700419437782227764059387198716))))))))))) + d ^ 12 *
    (36778573002467808130534410743287256164837673117050406 + d *
    (-17912584119276992421179285849140555771020132648611388 + d *
    (6477274088439710119271894013146201909939639192225213 + d *
    (-512743568030686401935943076789052822778085260252160 + d *
    (-1968312614708006443057219938143238283920717319922999 + d *
    (2532149800127023155061043119630250669209625700676909 + d *
    (-2224540302719788931236786057950025623198815297164027 + d *
    (1644514309889282162147783338152292969153536130914447 + d *
    (-1082957706351660685488763396720194976891095056810976 + d *
    (648004416741954152092825947089544877909434871090419 + d *
    (-353103479085757369974106496499014916407069023352945 + d *
    (172516016038920535045412480741391321261650580236401))))))))))) + d ^ 12 *
    (-71842848724407190815257781433863017281449554154966 + d *
    (21249820680294199644030221720723282151097323976885 + d *
    (853007013615326651926444557187058385156483611155 + d *
    (-8305280871540916591076485393690957371186493431146 + d *
    (9115016276604504320771677511171274573607686177067 + d *
    (-7482090706208950587787746729648120430671598391203 + d *
    (5370415590581175372076731902040434558293700709616 + d *
    (-3547758694966073836535213356871934700649774326550 + d *
    (2208049482048792240576387945422046688395870764088 + d *
    (-1311139718900912715653866852013314220328356621915 + d *
    (748480470785358864057985162545515918375922962248 + d *
    (-412795217509410534771962768840517305169705568205))))))))))) + d ^ 12 *
    (220651440640124727695811127781929698776284890471 + d *
    (-114555674344775643144477660905599575086858881008 + d *
    (57848028025293762090873427768047912807045592715 + d *
    (-28440533760935908768856443453753808769605628589 + d *
    (13620577893379266518511527782278054057734050271 + d *
    (-6355341136468450128797478508437748037653386230 + d *
    (2888865903281167214998582258183125435883125741 + d *
    (-1278819154072928321730387395724152438408852849 + d *
    (550930441541663324802217033095824973848607750 + d *
    (-230755618205122580887808263777585622600447489 + d *
    (93837057556729954862267065695586922198664277 + d *
    (-36976979557144091895806087122838445272871645))))))))))) + d ^ 12 *
    (14080275564744623804981447019774528580075704 + d *
    (-5159465652065714697418565880074790094351162 + d *
    (1807907001667341437559823389405652468782923 + d *
    (-599721469664783132410453230550771188581977 + d *
    (184979773297617138515191546052838677374680 + d *
    (-51105211953542517081826802632740327857681 + d * (11438594281333899652451610885869181386810
    + d * (-1228755468335022954887114537909485786946 + d *
    (-679662960745609158913278744446835662329 + d * (654341973009810747326860002274024208821 + d
    * (-376179033606794610974675527099406693707 + d *
    (180525630651426104702206958014802904466))))))))))) + d ^ 12 *
    (-78293108212945904981239948020092300942 + d * (31662986285090987219534612752409172911 + d *
    (-12123900572106781190591235292761571870 + d * (4431611775305111638399887910224922041 + d *
    (-1553596884190953113400061896489118062 + d * (523809924475858703037728588333478489 + d *
    (-170114208355370861516104755402462816 + d * (53234149973987322919493356295367341 + d *
    (-16034707315972032823264990327522648 + d * (4638123189312257506377210524129388 + d *
    (-1284626880461039919467773392314815 + d * (339733358017072525380219739687582))))))))))) + d
    ^ 12 * (-85512379033554952918110043206993 + d * (20369104557916509166824261112288 + d *
    (-4540315928867594431029458621342 + d * (928920093859271926701449591537 + d *
    (-169436038700936180995156586396 + d * (26412204485697796114108059898 + d *
    (-3285761227405107265476998658 + d * (280443031007431530661071302 + d *
    (-7406430238817445870794763 + d * (-1780172562269809313959846 + d *
    (206572484258403658591694 + d * (6720511315039909451021))))))))))) + d ^ 12 *
    (-396725710502646551122 + d * (-1314591539959731689736 + d * (389216354970424525764 + d *
    (-53083465784451988907 + d * (3046550850079004367 + d * (137428306700631213 + d *
    (-30957094621911531 + d * (1029776932192456 + d * (12902165837031 + d * (12069231098439 + d
    * (-531340538205 + d * (-171556885997))))))))))) + d ^ 12 * (5126354797 + d * (1235285812 +
    d * (58452418 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_35 (d : ℚ) :
    orderSevenSelectionPolynomial d 35 = selectionExpandedAt35 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 35 =
      selectionNumeratorAt35 d := by
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
      selectionNumeratorAt35
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 35 =
      selectionDenominatorAt35 d := by
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
      selectionDenominatorAt35
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt35 selectionDenominatorAt35 selectionExpandedAt35
  ring

private theorem selection_cofactor_eval_at_35 (d : ℚ) :
    (selectionCofactor d).eval 35 = selectionCofactorAt35 d := by
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
    selectionCofactorAt35
  simp
  ring

private theorem selection_factor_at_35 (d : ℚ) :
    selectionExpandedAt35 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 35 *
        selectionCofactorAt35 d := by
  unfold selectionExpandedAt35 orderSevenDualKernelPolynomial selectionCofactorAt35
  ring

theorem selectionEvalAt35 (d : ℚ) :
    Internal.SelectionEvalCertificate d 35 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_35, selection_cofactor_eval_at_35,
    selection_factor_at_35]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 35 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt35 d
#print axioms solution
