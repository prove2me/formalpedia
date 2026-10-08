-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_25
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:02:57.86941+00:00
-- url     : https://prove2.me/submissions/fc4882eb-63a1-42d1-8a73-b8a6d060fc0f

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval5.At25. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 25

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt25 (d : ℚ) : ℚ :=
  -107171875000000000000 + d * (-13618995750000000000 + d * (23314638042972000000 + d *
    (-51417711507562937664 + d * (83080941863954580864 + d * (-54159747608114787456 + d *
    (3331591584839501760 + d * (25960796103351668544 + d * (-38608666376907686976 + d *
    (41067472013752299712 + d * (-29894301875417663808 + d * (15484208828744233728))))))))))) +
    d ^ 12 * (-4968257000418649536 + d * (-2004825208273339584 + d * (6100086677985650304 + d *
    (-7167269272719849216 + d * (6301810670886542976 + d * (-4822640876735738496 + d *
    (3328888676710391296 + d * (-2076776030932724544 + d * (1194784779705130368 + d *
    (-648790354679584128 + d * (328744945919321280 + d * (-151542564232771008))))))))))) + d ^
    12 * (64145678635600320 + d * (-25975405760143680 + d * (10055193350225856 + d *
    (-3460533357818816 + d * (1000997444147904 + d * (-267813336111936 + d * (85218826660032 + d
    * (-30176757763776 + d * (8448718335168 + d * (-1567088498496 + d * (263589970368 + d *
    (-95471163456))))))))))) + d ^ 12 * (34168868544 + d * (-6124566336 + d * (345542976 + d *
    (-48727744 + d * (49978944 + d * (-10578624 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt25 (d : ℚ) : ℚ :=
  -127014404296875000000 + d * (-17181384656875000000 + d * (35976413813842000000 + d *
    (-82644601149592905600 + d * (135722256124918602944 + d * (-111243615403522750528 + d *
    (48702993123864150528 + d * (-8018574387003775744 + d * (-16359654683242170624 + d *
    (35776541471364292672 + d * (-37765177117772231936 + d * (28480113073400433792))))))))))) +
    d ^ 12 * (-18221944906399601600 + d * (9186426672621363904 + d * (-2013551408490602496 + d *
    (-1653910703350148608 + d * (2457336604531554368 + d * (-2122351982034694528 + d *
    (1534548216988947328 + d * (-973077349487477504 + d * (571148712793326848 + d *
    (-332573567881882752 + d * (189924693038545664 + d * (-101622516884995328))))))))))) + d ^
    12 * (51688179551949760 + d * (-26146483798180032 + d * (13042749982429568 + d *
    (-6164859231508608 + d * (2749313842085440 + d * (-1178488455692736 + d * (481063220941824 +
    d * (-181561780282624 + d * (63180999310656 + d * (-20756485987712 + d * (6382010461568 + d
    * (-1698356695040))))))))))) + d ^ 12 * (346809186304 + d * (-45455397376 + d * (1979492352
    + d * (395554816 + d * (-51548160 + d * (-1335296 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt25 (d : ℚ) : ℚ :=
  253965128883220299030654132366180419921875000000000000000000 + d *
    (-11772024344401879226092994213104248046875000000000000000000000 + d *
    (5420247546117956224496642161178588867187500000000000000000000 + d *
    (16356095290254593684286906371262323242187500000000000000000000 + d *
    (-30861019905756321605935776559491585805078125000000000000000000 + d *
    (45722436064687874114586226924095014859293875000000000000000000 + d *
    (-26420616852915138205423240564793387052189145720000000000000000 + d *
    (-33626769352096174776740555847735072721967906725652480000000000 + d *
    (93742355074341399298018027077506182677017700843217899520000000 + d *
    (-122017849394883226646450939860225958049013171212939261345529856 + d *
    (97622189950411718497084617755783643564387509468233545880698880 + d *
    (-13804172779012923137735093575549068867813119123111570681102336))))))))))) + d ^ 12 *
    (-94914652255143946543488679004314149713202940053872885713862656 + d *
    (174485893900026000257648294699973281486482913963264710803193856 + d *
    (-189817868346245062083380575762819719835826248010061191092633600 + d *
    (131509993545606865126214887085258634776994477938442791520567296 + d *
    (-18542671421671602662284681768203505560662508789740855988584448 + d *
    (-105374802747766608364786726306121699471045103856102840389074944 + d *
    (194970934781081041764899601461676215182725882106361991905935360 + d *
    (-223653478267071823532610446258020928292260540114875042940583936 + d *
    (188384866749620050933557607108109354306432654123215832182947840 + d *
    (-107193527245615279596423584832870307317689693143095879345635328 + d *
    (10510907167921868303100812414662159788460197323310177433944064 + d *
    (72204059871062208008455452260323238458885342502898113982496768))))))))))) + d ^ 12 *
    (-122203588777566926081482370938438690976486991496629547031330816 + d *
    (134237108279839202871670137867222164357836539301962372966514688 + d *
    (-114673604545042933532618815933521477901982395164619013406064640 + d *
    (76678920059647093685296006861404107630426034993606328843239424 + d *
    (-34364941301567375842613318174398946552261282324767424583565312 + d *
    (-1496654137291252105472835288537361751329213457774296262508544 + d *
    (25207982057678498843632839627594531216647498679228686021689344 + d *
    (-35887671744291716992151396292030137902198753952862969437356032 + d *
    (36005739901504140787159556982422245181345138664747458527494144 + d *
    (-29506729010640755507636920505265942837118317843590553015156736 + d *
    (20262602845285866524713159453119274011949354899285594144505856 + d *
    (-11187627702731122265579985081281907222714143346270773604515840))))))))))) + d ^ 12 *
    (3959472415921501328591510542022863370524753926238222777057280 + d *
    (841503682473402977938910043002063493575523205492491122376704 + d *
    (-3383538440023895947537765497498788242005506943319881212231680 + d *
    (4211051921996577213770144560024546470819377928842558825037824 + d *
    (-3957283776995723133386097255567543024088208586278124819316736 + d *
    (3170926760618062747427546505489703586244798197715956314406912 + d *
    (-2242893935957834324671896335569728510983497584507626791895040 + d *
    (1402888920168699155093815843210990423780470110289148913123328 + d *
    (-752412327051321146010807022603788946047534054542386564431872 + d *
    (308205266560049487857115656741448259373201434167265903247360 + d *
    (-41334051450414233322343991967612541786896131050260484325376 + d *
    (-94171018479304047044671326574915504673081994637400107122688))))))))))) + d ^ 12 *
    (143897315271485194284741501189958197895952273694216149008384 + d *
    (-144737671039365614519881891991033070424305762736920648482816 + d *
    (122626657779194961237624827283837201725484729709501863952384 + d *
    (-93593827961882661080999484341353975362899364301036896124928 + d *
    (66166236073951028875647618241732100891175442276856066211840 + d *
    (-43911388797652810808709769266124108834901258920072749514752 + d *
    (27530502403343807872259721073226332495079997257422511538176 + d *
    (-16332511352864904519463853464669561647077370014844409872384 + d *
    (9143124107520568618809717585318930936851527261710814019584 + d *
    (-4788496541959074735647841646834868225171117183388602073088 + d *
    (2301419730899273316985413116561707391578365987926777790464 + d *
    (-970179410657610360298280915985546202547629632780548440064))))))))))) + d ^ 12 *
    (312347334632306589340688630993733981746244756143147581440 + d *
    (-22488087429464948282851525920687765022825846916576182272 + d *
    (-80964164197241247398946817960438459812343251533313343488 + d *
    (99221220385975543689528469466969274811642670760039022592 + d *
    (-84731525230364826214523856115859616412497794362562314240 + d *
    (62224507202077930599975647098238624651275245737871671296 + d *
    (-41758920400929642858217467168404575355547699792111730688 + d *
    (26284962309219305050932685397875028758446860870437044224 + d *
    (-15727719067550759102388880611986281369118950338768404480 + d *
    (9015011991861623195105207525703264300257039367734034432 + d *
    (-4973234584848859262993695480131845361404681890316943360 + d *
    (2648134050743134720367399970777457912902179752842100736))))))))))) + d ^ 12 *
    (-1363392855443402357766028555253185253478655088779329536 + d *
    (679309416569605693252781152981500195151301692598255616 + d *
    (-327617030458594733016505953723422108023893000816427008 + d *
    (152870667139622097876999684854151197338732273074700288 + d *
    (-68935247277271440434691101499139718347119768882642944 + d *
    (29980029716761485997478574863841768005802865019322368 + d *
    (-12533197419907554303104517839791745300521741800964096 + d *
    (5009989447130233731620112666289887912561556964245504 + d *
    (-1898321094490142469931027614701189735748054518333440 + d *
    (671343529600152439305501873088012536902999924539392 + d *
    (-214830940196609031538352689143876019744238790508544 + d *
    (57575645074566275299290840225252163513946107543552))))))))))) + d ^ 12 *
    (-9403519303903681934178197086379398804579223601152 + d *
    (-2325186997048972175688274838497421134778425147392 + d *
    (3479993194087338466199845989164022691732286865408 + d *
    (-2396231131774689574147442361171988921464725176320 + d *
    (1329024255215987253526929213068856887171895001088 + d *
    (-658318034235731268183246944163367235756211044352 + d *
    (302498150387680865647927820435984991615022006272 + d *
    (-131285401178288974235436466131388132920078368768 + d *
    (54344546557581908537342980616479309658017759232 + d *
    (-21577887351700570375270809179759872868720312320 + d *
    (8246123756287195521826809569187075975990738944 + d *
    (-3039006776451356996928636705814928051382517760))))))))))) + d ^ 12 *
    (1081114251102238951676678323066424525768622080 + d *
    (-371320963005658727047070939941032691154550784 + d *
    (123074557109018122243610240034256761568362496 + d *
    (-39327422474747573973547587474898966986620928 + d *
    (12097063292514433251655496169133522317475840 + d *
    (-3574627722917403891521038592697218794782720 + d *
    (1011939491778602547512231452728270013857792 + d *
    (-273440340941169742966532046909980020310016 + d *
    (70187917813761682000591979846163769065472 + d * (-17006677589982829373725836429725555752960
    + d * (3857806276116584533842836477885131784192 + d *
    (-810187481626535211021187602570505355264))))))))))) + d ^ 12 *
    (155081910646470274650928149291453906944 + d * (-26432483335997797248852549849084329984 + d
    * (3860768750906433172687053111309107200 + d * (-448137472220841588311946320033087488 + d *
    (33157655984474566422050209408221184 + d * (488538961131205108566645009285120 + d *
    (-580167844480381891017771727454208 + d * (86668928799837030786688363790336 + d *
    (-5577028891377892633767725236224 + d * (142180774000002370259096961024 + d *
    (-128554183322127997783755980800 + d * (51731384080326166332657631232))))))))))) + d ^ 12 *
    (-9318537983308691213245743104 + d * (744491449382249713147576320 + d *
    (33973073506141384454176768 + d * (-14895435975297210980237312 + d *
    (1370325451625757767630848 + d * (-5965841908769188741120 + d * (-6888681365548493963264 + d
    * (150891826335158108160 + d * (11651659646641373184 + d * (4951738681642188800 + d *
    (-302116674417459200 + d * (-55333284976525312))))))))))) + d ^ 12 * (1611800481103872 + d *
    (345190736592896 + d * (16128744357888 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt25 (d : ℚ) : ℚ :=
  8189280586934355454786782502196729183197021484375 + d *
    (-378602632791180716509416015469469130039215087890625 + d *
    (126852632540488380031905035139061510562896728515625 + d *
    (634599884792550910551372249891050159931182861328125 + d *
    (-1015039710242397150036121796816939115524291992187500 + d *
    (1232240280078579386142883916720186377048492431640625 + d *
    (-328485358911003393416861730255954318121795654296875 + d *
    (-1639475084312750640704857536195326649898164628906250 + d *
    (3119893898366665380888467464332807387380200814375000 + d *
    (-3170007310370207692418618955717458168237346117036924 + d *
    (1609212712424263998078690371595199206717997956602760 + d *
    (1195954836979588859963936414396822395223186034058451))))))))))) + d ^ 12 *
    (-3883966419585118309817712087731493084572134846584768 + d *
    (4989053249124039725351860237050975560357272076487154 + d *
    (-4065599814670155305931448294799729522118016110982847 + d *
    (1541219870715063348972327697707091690125054714822746 + d *
    (1613339589663387508947065884187056734123140502312252 + d *
    (-4179209440590505538061145944052278523379615674725382 + d *
    (5293203583026872345524587133657413555768215728984477 + d *
    (-4792475647767717587582678730955497125026333550053287 + d *
    (3071017224063908927269189312169863175137949395779033 + d *
    (-825078219740458154662761772852538468167474836604229 + d *
    (-1210171416407692421188340228835866533642598296445317 + d *
    (2529274766741674216224150430830201862597609295377744))))))))))) + d ^ 12 *
    (-2971753298930910059077747431851612101194233430077510 + d *
    (2662005955294742436779670304152079671589145320775406 + d *
    (-1886840640396229735683582089869506853994017327390895 + d *
    (968503142317794316022130303078049965553427024328983 + d *
    (-160389961652137156386396404318526891652155228406459 + d *
    (-400221888732997774144638435891676110773685356561191 + d *
    (684102764460969152590141715521189062334284135769906 + d *
    (-736076964393069368624896092461953067083951821969625 + d *
    (635763253440575368743346986266997844250623746811201 + d *
    (-464130478991901559977677067296235304057198773938515 + d *
    (283543752861173448763459917282095097541819636208756 + d *
    (-131647112938595361452777157953692085408418512180416))))))))))) + d ^ 12 *
    (23941468149110413332183875069675765659718659722606 + d *
    (39747081705247188071388396501600320633624760758792 + d *
    (-68079458165342698704312622394914483086651736224027 + d *
    (72419308809467798816456024491023468059603503773650 + d *
    (-63260471016330460801799239049057737708769134114339 + d *
    (48578851317947652256315891669190104572708839298209 + d *
    (-33497203863291281498506043575111840585118750238157 + d *
    (20701146679433219575872826451601096739755630391127 + d *
    (-11145127106943952279670528365981579206715180012466 + d *
    (4743898295521976851541447941803186470422293969519 + d *
    (-913941923651197642061487863001974631139261149935 + d *
    (-1065167206366942218773796989387100349578610891289))))))))))) + d ^ 12 *
    (1849833689258907015550226906507121938644385267294 + d *
    (-1949360437300918174520463804621731187679452880025 + d *
    (1714582707215930334176539444565349243514200229495 + d *
    (-1361881088285114645667283642146784024015797982086 + d *
    (1008909408764518787918399208552817640581194113677 + d *
    (-708742019039611734515184108996595799713474785673 + d *
    (476700747093056617928533442620598660437577186196 + d *
    (-308873187532629022135959401463677242304623094620 + d *
    (193577046679089176106061834081350014330900158758 + d *
    (-117671342886372282898400899145064489094511819675 + d *
    (69512242218670596784678662056083725676146885438 + d *
    (-39956650479299497105623249429959445085829574935))))))))))) + d ^ 12 *
    (22367439948373620818551522680135730343862064501 + d *
    (-12199695746461834609701596632832659410873714038 + d *
    (6484344265672863248282730692825810071712501345 + d *
    (-3358403974839846248640574437491647866786700539 + d *
    (1694357361514118133105441205091109291422898901 + d *
    (-832191386791347825799293110653724269500106960 + d *
    (397556116552668846237784977351768082133855061 + d *
    (-184492670735214326082405093782120591925849919 + d *
    (83022642517571616297317161256346487723429840 + d *
    (-36138939499854243724700113794598430481401799 + d *
    (15162680330028540348679415020690397873487277 + d *
    (-6099566334781472766679277276675591558590055))))))))))) + d ^ 12 *
    (2332940163980615447799715586491335021903754 + d *
    (-836265729292440488252611622414787891572392 + d *
    (273232984027298949041702499015078927473543 + d *
    (-76170742164115932700061858781497743363357 + d * (14240464528619021688670505547597908242660
    + d * (1682971424590517379469081307293452238109 + d *
    (-3820044324613463166181761090945758503720 + d * (2790535209549965916464921575090255933994 +
    d * (-1591596049528695949690991974387288200009 + d *
    (803153258156487256838927439778229460211 + d * (-374439036603277901176636237400275069307 + d
    * (164534185449614995534292797687983669516))))))))))) + d ^ 12 *
    (-68872011081937886750580712043380745952 + d * (27629839455348063909412488448955429011 + d *
    (-10660979585115487459370863780269020070 + d * (3964283884220756663454390679594513811 + d *
    (-1422033713212042941620037479155818392 + d * (492187370551610718121696148962908169 + d *
    (-164290129447441368409565545188214456 + d * (52820635418635801625978900313351741 + d *
    (-16323989812939407266169531329003548 + d * (4836392971821857954048673540587058 + d *
    (-1369289424843901694467532612522555 + d * (368984083569854638837171183743902))))))))))) + d
    ^ 12 * (-94103427755435181089330235434843 + d * (22518075350014598838234274221558 + d *
    (-4989818889304378788931946538882 + d * (1004736798498668357983145726837 + d *
    (-179050011518398619398743977356 + d * (27186927614725609233186853288 + d *
    (-3305730978965741072517178738 + d * (281877778048967304279713932 + d *
    (-9685798297949614005804863 + d * (-1086164277897371547190416 + d *
    (103538914156709168591184 + d * (12739182358256979033981))))))))))) + d ^ 12 *
    (210240940236710765788 + d * (-1457988877027238800416 + d * (397263478564162783184 + d *
    (-52738970995779456657 + d * (3026708218173533167 + d * (131763912257201603 + d *
    (-31036805321584231 + d * (1118456680650686 + d * (13846202069651 + d * (11466383007449 + d
    * (-571545838555 + d * (-173068766017))))))))))) + d ^ 12 * (5081885017 + d * (1234777812 +
    d * (58452148 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_25 (d : ℚ) :
    orderSevenSelectionPolynomial d 25 = selectionExpandedAt25 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 25 =
      selectionNumeratorAt25 d := by
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
      selectionNumeratorAt25
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 25 =
      selectionDenominatorAt25 d := by
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
      selectionDenominatorAt25
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt25 selectionDenominatorAt25 selectionExpandedAt25
  ring

private theorem selection_cofactor_eval_at_25 (d : ℚ) :
    (selectionCofactor d).eval 25 = selectionCofactorAt25 d := by
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
    selectionCofactorAt25
  simp
  ring

private theorem selection_factor_at_25 (d : ℚ) :
    selectionExpandedAt25 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 25 *
        selectionCofactorAt25 d := by
  unfold selectionExpandedAt25 orderSevenDualKernelPolynomial selectionCofactorAt25
  ring

theorem selectionEvalAt25 (d : ℚ) :
    Internal.SelectionEvalCertificate d 25 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_25, selection_cofactor_eval_at_25,
    selection_factor_at_25]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 25 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt25 d
#print axioms solution
