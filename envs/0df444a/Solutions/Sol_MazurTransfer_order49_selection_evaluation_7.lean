-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_7
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:53:58.322988+00:00
-- url     : https://prove2.me/submissions/d0e4bb7b-6b53-439e-82b1-3c98bb08a395

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval1.At7. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 7

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt7 (d : ℚ) : ℚ :=
  -27499853269504 + d * (-24500598135552 + d * (110274241537152 + d * (-224142276194880 + d *
    (151989704471808 + d * (508977960734592 + d * (-1933058011622976 + d * (3536229559569984 + d
    * (-3870491536353600 + d * (766220714360512 + d * (7868612029464000 + d *
    (-22740715022045184))))))))))) + d ^ 12 * (42571070158734912 + d * (-64332534817161408 + d *
    (83942439071614848 + d * (-97466697238977024 + d * (102428868549936768 + d *
    (-98401274054925696 + d * (86877051723276928 + d * (-70715109339804480 + d *
    (53174593664080128 + d * (-36928771277027712 + d * (23610704155425216 + d *
    (-13839723148870080))))))))))) + d ^ 12 * (7412975267899584 + d * (-3611635269429312 + d *
    (1584650423644224 + d * (-619435944172736 + d * (218366953139520 + d * (-74333102252352 + d
    * (26622845906880 + d * (-9614734110144 + d * (2996290276032 + d * (-739550549568 + d *
    (174107774784 + d * (-57116945472))))))))))) + d ^ 12 * (19385189184 + d * (-4180234560 + d
    * (461954880 + d * (-87421120 + d * (47407680 + d * (-10620096 + d * (326592 + d * (122496 +
    d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt7 (d : ℚ) : ℚ :=
  -32579888147520 + d * (-32792380258624 + d * (169658599769344 + d * (-410961327791616 + d *
    (558957914043968 + d * (-54848674997824 + d * (-1601013196746624 + d * (4186824888616832 + d
    * (-6827285381886336 + d * (7800847828691392 + d * (-4831419938229632 + d *
    (-3532003268401920))))))))))) + d ^ 12 * (17146320549105088 + d * (-34095086603320640 + d *
    (50801253662448768 + d * (-63274500035900800 + d * (68937145454648384 + d *
    (-67486732806163072 + d * (60592355556088192 + d * (-50893605124148480 + d *
    (40751113520477696 + d * (-31507379128121472 + d * (23608471595303936 + d *
    (-17085054558440960))))))))))) + d ^ 12 * (11863236308797504 + d * (-7849462126042944 + d *
    (4920264194912768 + d * (-2906178701955840 + d * (1606927191530176 + d * (-825254780336832 +
    d * (390846904348032 + d * (-169761598340992 + d * (67078100377920 + d * (-23683053348224 +
    d * (7229889428864 + d * (-1816141054976))))))))))) + d ^ 12 * (348539628544 + d *
    (-44195699200 + d * (2007638016 + d * (370524160 + d * (-54073344 + d * (-1353728 + d *
    (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt7 (d : ℚ) : ℚ :=
  4220689670923864314312198043026441109504 + d * (-167686766469960457880534527093002140123136 +
    d * (-661027715447135856733189951634740917305344 + d *
    (3364684733579640359874853312353582675656704 + d *
    (-1539992063014543552908705300339943660584960 + d *
    (-28557765361735226674658063817398794939793408 + d *
    (113558826023288338829341949378964271692775424 + d *
    (-162497836139241576464132829525072682239918080 + d *
    (-268849856163185843677386187749811888517808128 + d *
    (1986444858797063659962288917755585986374926336 + d *
    (-5053189818373351378150175907568973192846901248 + d *
    (5583196852220624932156491399147209433115525120))))))))))) + d ^ 12 *
    (8561687293712102646172200773959960754991398912 + d *
    (-56716664155970189082016888934684285031473741824 + d *
    (145847987138480777092225989828116653174725017600 + d *
    (-219849263210957911176181700243888800197017337856 + d *
    (87055693693079942810268630391924294330072694784 + d *
    (611000976426982419221100856832289209571019587584 + d *
    (-2256311834286279804234930400455419495679487115264 + d *
    (4775692627830785920458083607968905078910594580480 + d *
    (-6778711642422971804548005039909416350573917634560 + d *
    (4603343384006881067324784035830902993155552182272 + d *
    (7902003716879905135891441444151744155419312652288 + d *
    (-37539355218139709365302936656155499667889624186880))))))))))) + d ^ 12 *
    (86568890899533402834304520658737523679176344731648 + d *
    (-143942449673436523566334184000722577148796448800768 + d *
    (175109416162149851992855575576952814076979836092416 + d *
    (-115738477581881699790420281165829622610300935602176 + d *
    (-122648856769274539427609058780441192543734817095680 + d *
    (627029075950847308804516647912341923447483128872960 + d *
    (-1433314665312305530172244457931740559190436100702208 + d *
    (2457868138840083642958744683123815123296521969991680 + d *
    (-3426691042257019121582601857929442573668179140149248 + d *
    (3828965700028650853527975470437705031555366514851840 + d *
    (-2924914497756892746544118672160391342255565403062272 + d *
    (-169563318696174824930674704158548093981248420577280))))))))))) + d ^ 12 *
    (6317757219888414883816706438106196118626895873441792 + d *
    (-16138524721243941739683371586111785578984879657320448 + d *
    (29770847979771977821547634561871239916376666857275392 + d *
    (-46687666624253774936584389910845257808456629920989184 + d *
    (65617696169414471257659473517143522689931140279042048 + d *
    (-84613502173806052853522471172504353027560351139627008 + d *
    (101270572723362135918908606552740225076812723976404992 + d *
    (-113065024347527466887119705221138311233136010779688960 + d *
    (117747591023255837681882687653290153700571098508689408 + d *
    (-113716947007074662616613575131192952092314634089922560 + d *
    (100299546056699339927832250756373870806434174045782016 + d *
    (-77883890839584052093934535492184936656793149552197632))))))))))) + d ^ 12 *
    (47888145732527805737270278787478227124096279178903552 + d *
    (-12573087328521051280892262927725972224091276460425216 + d *
    (-25260043712671479851979544356380323558850794481254400 + d *
    (62630365772538841988455397920749028239885263384608768 + d *
    (-96736264347675967041228980256381077017481618676252672 + d *
    (125259233394271910465265600399069107232886504372568064 + d *
    (-146575214681243194666004573461207089487505204239138816 + d *
    (159855612108178546548476243847185578274430361897795584 + d *
    (-165059401965941736508764924691215553068442210668118016 + d *
    (162833371515581492178702038794188103824661105593024512 + d *
    (-154347659022275273988639266435420113425764373557936128 + d *
    (141098000252618454757823206930437619984873043628654592))))))))))) + d ^ 12 *
    (-124705035417957974695163553517208313977866000340090880 + d *
    (106735949202822351028768913422573063205237826153086976 + d *
    (-88566110141858672103288515276082363330791450243235840 + d *
    (71289755351538272421319728453440625424265599178768384 + d *
    (-55680500222936712416739553738704501698461608153972736 + d *
    (42195651621433956841985847602040265986834968607981568 + d *
    (-31013714903003030397367896519515314661244723079675904 + d *
    (22092409528014279442857595809547288115128426352082944 + d *
    (-15234782418382006495277495834527511582376649103507456 + d *
    (10153088031876629256448238158078821270760855217897472 + d *
    (-6523226564620346733986540272904646366031415187603456 + d *
    (4025910778158500474710175486646961339002117181669376))))))))))) + d ^ 12 *
    (-2373726541604994078983791828890400542436809358180352 + d *
    (1325464446172713801152850536383521536589752832098304 + d *
    (-690392837402853436330178938981354381871255074111488 + d *
    (325592920708175399881221042118863643705416214380544 + d *
    (-129292577955510489167849059978775417862822275317760 + d *
    (32571853556244406061190080005682780990463625134080 + d *
    (8896442057512035511375440333837869382224725409792 + d *
    (-22089040711331002495068738568173268613651581632512 + d *
    (22426953406158348681882811409182454125521307172864 + d *
    (-18075722150077172401672810542715362887034948550656 + d *
    (12927751458709500993570598780634289550051396550656 + d *
    (-8539823832057685962317709386624013882468499718144))))))))))) + d ^ 12 *
    (5309796995986939409691463494372001333286794166272 + d *
    (-3139649056348179434137250875779243327237873991680 + d *
    (1776280407156953828218999953777698284169182052352 + d *
    (-965206628918379761147106237891964590073873170432 + d *
    (504954202134681408195775307130094982568246247424 + d *
    (-254714865634443226795538898146089921322207674368 + d *
    (123992824376648589063536365535592568384493715456 + d *
    (-58269293851075029371329553211315282401078018048 + d *
    (26434954287608824590807231904113652730211860480 + d *
    (-11573539594876585816674054166686461354305650688 + d *
    (4886838394404144756351103033817027324690038784 + d *
    (-1988230387757117541869104053849256267101765632))))))))))) + d ^ 12 *
    (778505590940773732551437341591262118047645696 + d *
    (-292928861081563928342553068079400012072615936 + d *
    (105724117915861435395882546777401426770395136 + d *
    (-36520860857833735322065858588398410919051264 + d *
    (12042502430458449402693281031714476293881856 + d *
    (-3778584389159925790991317485799694722400256 + d *
    (1123913990012358687525652973611318651650048 + d *
    (-315463142059840252944623293486404643848192 + d *
    (83095047655950978671895009579383438442496 + d * (-20401596341422891032245393242242136145920
    + d * (4629313941311178791103674856063652855808 + d *
    (-960145727102614542125456949153741406208))))))))))) + d ^ 12 *
    (179307407887435889724690172813795131392 + d * (-29495288539095798587333745659231338496 + d
    * (4123059457292077392489039986055184384 + d * (-456547755446116824351602748029403136 + d *
    (32834733030659812159847901083729920 + d * (96323753485147192008592631267328 + d *
    (-410448465227162295387987406749696 + d * (55338676032837572547202715746304 + d *
    (-3109089062017781680785196843008 + d * (352150759644368573495950442496 + d *
    (-211318022541054206497605025792 + d * (61137817500451978583317938176))))))))))) + d ^ 12 *
    (-9514982710873586209873461248 + d * (677916731850777613145210880 + d *
    (39540490434670504450195456 + d * (-14723038262137847247798272 + d *
    (1360029240944413713891328 + d * (-10953388195439950692352 + d * (-6833007409076963115008 +
    d * (212667546479788818432 + d * (12012864277762277376 + d * (4605341426681643008 + d *
    (-324036366467858432 + d * (-56162824095268864))))))))))) + d ^ 12 * (1588065604730880 + d *
    (344932912726016 + d * (16128649986048 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt7 (d : ℚ) : ℚ :=
  5132500269915507257687362903193 + d * (-201643440121161391078207099479869 + d *
    (-897325935856677239907826454281995 + d * (3867726536004519812295882253606829 + d *
    (502034622837781274004679514761568 + d * (-38272234609866612926046917524345801 + d *
    (122503408993658148109563865016176591 + d * (-108859741552178510331696356214072320 + d *
    (-501565138807463042652604223950858420 + d * (2335743118220297293228506995215269978 + d *
    (-4661332438813088493363469489317316938 + d *
    (2308652923732861296335788180274893373))))))))))) + d ^ 12 *
    (16593044348452048572800036475661555608 + d * (-64711037917335588129678747178451066534 + d *
    (131358328825713853142638060357868702863 + d * (-138101181318832591285787111731737076882 + d
    * (-100790207620978542216044202735284573070 + d * (844954872930566919986073182005544467940 +
    d * (-2223228457122091731149497626550886863607 + d *
    (3795888846489378676747633411336369187601 + d * (-3978804039862552483134360070132503328005 +
    d * (-297820838028025502216881579089261533177 + d *
    (13032349049090684520780154326164060403839 + d *
    (-36959386091027397620392887558029353228394))))))))))) + d ^ 12 *
    (69404119320586693012852525184968421554192 + d * (-96921042370496351336167400398407200216124
    + d * (90969635989626557814757153782890704886503 + d *
    (-8255437177699303454982582086487895342855 + d *
    (-200284527789198811428299808524779231922593 + d *
    (569335803715044820261801723327584931999823 + d *
    (-1088854842078802991414852365789648571263478 + d *
    (1669198934707500103895502131025626117054033 + d *
    (-2111781430835616084457722370946434325893895 + d *
    (2097291387032048516742272891070270516162419 + d *
    (-1201677751865206294256996339652394667596744 + d *
    (-1055765132846753063473764638147463679630516))))))))))) + d ^ 12 *
    (5136379831902977799604857665864065442271390 + d *
    (-11390950662018597858934543679469247419719908 + d *
    (19971942978300098616611338768485869835924213 + d *
    (-30768927903304202472518917589707257294883060 + d *
    (43382909222078778313727931629377513768214009 + d *
    (-57147228270058673211851663693951915389480819 + d *
    (71192952718378900326814208274640549913821145 + d *
    (-84547714019718657093615977611531101146854849 + d *
    (96250898893939459675793640123250562022201964 + d *
    (-105465994679489521365120892532354274838793637 + d *
    (111572731300771419544713251065465702856060107 + d *
    (-114226572891389135292154998354986195692397963))))))))))) + d ^ 12 *
    (113379694920208314577364247566304620306640626 + d *
    (-109264326526607694156443006066038714160982143 + d *
    (102344958080161262182924373118289228335941491 + d *
    (-93249585405078418373963019394983748839278178 + d *
    (82691605633790019042552609037422892638808423 + d *
    (-71393401290497675176066064845531790267942815 + d *
    (60020571906699658481466135778936177577294568 + d *
    (-49132836968773110524228159435945665010157970 + d *
    (39154441364406035397969501789021848063165700 + d *
    (-30363924594588870049753550698821219561983219 + d *
    (22900708850881780107670648063185805309172484 + d *
    (-16784330288031221713732295730460395914495705))))))))))) + d ^ 12 *
    (11941371388250031001104112113484936604348203 + d *
    (-8235215145029094308541084181469316238643060 + d *
    (5494480890620037388624015220050771621181159 + d *
    (-3537175174037948375029403000683528567749633 + d *
    (2188921270946861123377556391928381523186779 + d *
    (-1294864456398335420381553202930655302931794 + d *
    (725807083307142431173783216940565275474733 + d *
    (-379723390638306916542042900571835040849445 + d *
    (180044385891242993228759391326562083573290 + d *
    (-72057986359003190911931638499302547371965 + d * (18539675281953797110312752040379217103477
    + d * (4584275770490136439517384412620482046743))))))))))) + d ^ 12 *
    (-12053932580981455463143902674233669984244 + d * (12350533792133555688237401679655103081546
    + d * (-9996892647500381796113097986399502575125 + d *
    (7166736185501675555598187329842451405791 + d * (-4739595396582156934483387172698480725680 +
    d * (2947216090598872551616163887232758399307 + d *
    (-1741085144212121246508188166240507001018 + d * (983113948728972661459528095846025222142 +
    d * (-532577200218741370141010232477619047561 + d * (277431207291785294653046605756715189881
    + d * (-139159201333683723869428325288310035723 + d *
    (67259062327464662625886112939884696158))))))))))) + d ^ 12 *
    (-31329047010480828522030226595568614586 + d * (14060237146787132320746390148338213583 + d *
    (-6075980422282481271050184050042156670 + d * (2525768062349175524334498734775321581 + d *
    (-1008656997451574158371614647005829922 + d * (386296331683220872837250410631072521 + d *
    (-141577774845919129281015193930399984 + d * (49525053270164902728787550831402397 + d *
    (-16482101234892959739245278019878984 + d * (5198074747301430943896317112534096 + d *
    (-1545953711060775383951814843741863 + d * (430966194197167905927206527603382))))))))))) + d
    ^ 12 * (-111763137176870693125751093763533 + d * (26707927035584003481346927412028 + d *
    (-5810762537326011449943275959518 + d * (1133105679346912072375700089433 + d *
    (-193872104716405407469353343900 + d * (28219393230209097326682620638 + d *
    (-3324761348870723437480416010 + d * (288800620839554958662450674 + d *
    (-14799598242717245282119595 + d * (241206023753344965159534 + d * (-79407411119447906463870
    + d * (22826811816780299917581))))))))))) + d ^ 12 * (1292865966442590546610 + d *
    (-1709680219819998600912 + d * (412196716296352031684 + d * (-52208887945563466383 + d *
    (2985866072202050479 + d * (122142638569667801 + d * (-31120607453962771 + d *
    (1280705068439468 + d * (15623610753095 + d * (10382301296651 + d * (-643913119753 + d *
    (-175790150053))))))))))) + d ^ 12 * (5001839413 + d * (1233863412 + d * (58451662 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_7 (d : ℚ) :
    orderSevenSelectionPolynomial d 7 = selectionExpandedAt7 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 7 =
      selectionNumeratorAt7 d := by
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
      selectionNumeratorAt7
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 7 =
      selectionDenominatorAt7 d := by
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
      selectionDenominatorAt7
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt7 selectionDenominatorAt7 selectionExpandedAt7
  ring

private theorem selection_cofactor_eval_at_7 (d : ℚ) :
    (selectionCofactor d).eval 7 = selectionCofactorAt7 d := by
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
    selectionCofactorAt7
  simp
  ring

private theorem selection_factor_at_7 (d : ℚ) :
    selectionExpandedAt7 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 7 *
        selectionCofactorAt7 d := by
  unfold selectionExpandedAt7 orderSevenDualKernelPolynomial selectionCofactorAt7
  ring

theorem selectionEvalAt7 (d : ℚ) :
    Internal.SelectionEvalCertificate d 7 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_7, selection_cofactor_eval_at_7,
    selection_factor_at_7]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 7 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt7 d
#print axioms solution
