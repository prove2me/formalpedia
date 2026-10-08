-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_9
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:06:58.682571+00:00
-- url     : https://prove2.me/submissions/5db555e4-90ea-46ed-ab6b-905fa273e8d6

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval1.At9. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 9

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt9 (d : ℚ) : ℚ :=
  -544297892769792 + d * (-319747013139456 + d * (1271254182863616 + d * (-2697731130574144 + d
    * (2792799525624192 + d * (1674851572087680 + d * (-11334391175800896 + d *
    (22169706649694016 + d * (-27541201361798208 + d * (19519899962183872 + d *
    (7527055114735296 + d * (-51955564028546304))))))))))) + d ^ 12 * (105825305332793920 + d *
    (-158499116736132288 + d * (199198527456239232 + d * (-220072524885341952 + d *
    (218905865415972480 + d * (-198721020278792832 + d * (165746895675238912 + d *
    (-127535834026939200 + d * (90844247657085312 + d * (-59946274335004032 + d *
    (36520375072079040 + d * (-20451127857321408))))))))))) + d ^ 12 * (10510234233504192 + d *
    (-4947370064859456 + d * (2111577389464512 + d * (-804493955214272 + d * (275403226670784 +
    d * (-90924261583680 + d * (31919459832000 + d * (-11391113903808 + d * (3478251758784 + d *
    (-826559305536 + d * (187375478208 + d * (-61754961984))))))))))) + d ^ 12 * (20979823296 +
    d * (-4397340480 + d * (449020224 + d * (-83121856 + d * (47693376 + d * (-10615488 + d *
    (326592 + d * (122496 + d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt9 (d : ℚ) : ℚ :=
  -644940437720256 + d * (-422616104088768 + d * (1928702781168768 + d * (-4643383390542720 + d
    * (6798355656407232 + d * (-3872388637395008 + d * (-6705184109197824 + d *
    (21957343671073024 + d * (-37235184678960384 + d * (45635015131327552 + d *
    (-38796005270698240 + d * (14177558631002240))))))))))) + d ^ 12 * (24312333780518976 + d *
    (-68853360712064320 + d * (108518808051110912 + d * (-133302489873951232 + d *
    (139389143287453760 + d * (-129429630401313152 + d * (109577178222437248 + d *
    (-86564060199678720 + d * (65238639678426368 + d * (-47585654134205568 + d *
    (33691556144489216 + d * (-23070901239801088))))))))))) + d ^ 12 * (15203122973444032 + d *
    (-9588261420143808 + d * (5754710234297728 + d * (-3269288157465728 + d * (1746930975699520
    + d * (-870851671222720 + d * (401907558961152 + d * (-170877191813376 + d * (66537374252352
    + d * (-23347424386432 + d * (7137483582848 + d * (-1803311116288))))))))))) + d ^ 12 *
    (348305709056 + d * (-44336222720 + d * (2004510720 + d * (373305344 + d * (-53792768 + d *
    (-1351680 + d * (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt9 (d : ℚ) : ℚ :=
  32952707110186132966351012639090424163336192 + d *
    (-1403835119025247475847802792656648027016003584 + d *
    (-2714374886475239748861905902794421582987001856 + d *
    (16824529163677240753436260840694183842588655616 + d *
    (-22886401762434927081585713181714519472118956032 + d *
    (-45292918409489682789407729459969395501842038784 + d *
    (293331672322877115340011575374142205400441946112 + d *
    (-641220363006857946613685811213730968749736984576 + d *
    (406850073082572164450641026557348852060279537664 + d *
    (1822441114171851434501482497856074258578530631680 + d *
    (-7161614265732698473671745739178100214376811724800 + d *
    (13392799046578460026731761792991563400905464479744))))))))))) + d ^ 12 *
    (-10785557182299036089909661677741043271940329963520 + d *
    (-18743385616653479570309390553121840813725322575872 + d *
    (91977097999897148559518868950849733832365073498112 + d *
    (-199172088855776255172613163718515594808537178439680 + d *
    (268710717003326808122218170823008887358731644305408 + d *
    (-145904841151519746336144255736478786943144258961408 + d *
    (-373376492478190762130649516128855858642317088915456 + d *
    (1417773126838782814192760104529135886150829074808832 + d *
    (-2827244529042558246104278793008040689574241916420096 + d *
    (3929016779292387611186413991362628231892795703689216 + d *
    (-3460335050594267220817533257003477603671567613820928 + d *
    (-173999960900120513442111991254678834918082090369024))))))))))) + d ^ 12 *
    (8196152950927994319750921176497505167807239078019072 + d *
    (-20385326367263344512968559712351613796618786071117824 + d *
    (33994673161446482193800706899796554142456440684281856 + d *
    (-43224252564732260186836802332187713785062587888566272 + d *
    (39839787782280907315207153824531282880106554177880064 + d *
    (-15255593645487532464426155485932112778811427138568192 + d *
    (-36135100854525870560332894461889266639751303571701760 + d *
    (113225943026056438721935488849156479986399048725430272 + d *
    (-205354578417203423865890758655777524430934116658577408 + d *
    (291675766058771746079668070963403004364516040486682624 + d *
    (-343580305441895312137123024289142485023091760364781568 + d *
    (330082979232725214346829954349524985901189901286113280))))))))))) + d ^ 12 *
    (-225085828730851492581860006722598293617442337754447872 + d *
    (14671708370672042441192410606188949742543324867723264 + d *
    (297608749070966141866427703333054000444779297501085696 + d *
    (-689037153864305271023231560416913353777295948887883776 + d *
    (1120239717091259173162370650775593276939231589125062656 + d *
    (-1541405169164949727879299523429142784603023525765971968 + d *
    (1900755339044488822298934255854266159968432241483972608 + d *
    (-2153325889131705183739015212242788617905923450233159680 + d *
    (2268177023951699592483264891336282907760550656076152832 + d *
    (-2232682858661895730874943321299530604789155232120045568 + d *
    (2053335898102649507192019472698158051185854920018100224 + d *
    (-1753306957034672467211651743136897498921899175439761408))))))))))) + d ^ 12 *
    (1367621408565808512610623592297880682353171725673562112 + d *
    (-937139463456648388922953275625884848443975891009667072 + d *
    (502547376695495587427039685120333029829502740757479424 + d *
    (-99339696274074018884107296686874295219227524854448128 + d *
    (-245597242125251292763110766049265400968541633504083968 + d *
    (515593969403599625057749800987494166599186418077532160 + d *
    (-704139941065367708789127339294100126894489339329773568 + d *
    (813537827125106710631818358984802446526252230624935936 + d *
    (-852759385889726711122923939051678180996335534412922880 + d *
    (834990076989874708679476294495301665372608291202400256 + d *
    (-775267761499861519413453285984086043075502025376268288 + d *
    (688497997554552765789860567682753893250586238960533504))))))))))) + d ^ 12 *
    (-587998248545902871191681539393701724956550651249164288 + d *
    (484609142496785779640580225042017728319519230966366208 + d *
    (-386325073369633694704255097340110894563976769256292352 + d *
    (298342375201266115652179388337102012039797779610206208 + d *
    (-223398708747059774200694718121461214637062097224597504 + d *
    (162276714189819584839210986714011398593668057994100736 + d *
    (-114361559325515923681859114380635519098405961455108096 + d *
    (78168641582207972477095214246360210245346404732239872 + d *
    (-51787824689208415071307754957631567794315604304330752 + d *
    (33218873823085743483677069137525255399323361744257024 + d *
    (-20595573256064383379616939167211810659880853274099712 + d *
    (12311622375943284023911893315958409354965669974900736))))))))))) + d ^ 12 *
    (-7069753362887375595990029858516096862303247737815040 + d *
    (3877764762587206320249170640190447646747720661073920 + d *
    (-2013127040656613182839467822052392011018253242990592 + d *
    (973394589918621452399196742226426704283645220749312 + d *
    (-424470217499298348326437084072415016349767105773568 + d *
    (153944596434910235816497060380642225900192459653120 + d *
    (-32894584479652484305383691190993392486885090656256 + d *
    (-13134079060052924336818949657760619938925332135936 + d *
    (24803793789669842415406808948774774402160979083264 + d *
    (-22885919017387372561454231106195487730701505658880 + d *
    (17097667992899502824903555085764427284984473583616 + d *
    (-11411458427718110782818481602469289630139995389952))))))))))) + d ^ 12 *
    (7058997378548904435561608710573080941394158682112 + d *
    (-4119191880135379935252342670762736374943978356736 + d *
    (2289657592864493926600764633597018544925577052160 + d *
    (-1219370664738276661999046292740027174782127570944 + d *
    (624414898445948359584401640898182817147579006976 + d *
    (-308152761800984625054980738032560648279385440256 + d *
    (146761267339604457141619228717705198131091341312 + d *
    (-67504509276692506886651942640344924807769620480 + d *
    (29994755199741385828502709713236680430131871744 + d *
    (-12873460651049879396185629906764844137840902144 + d *
    (5334359756696381268236520530943831507876446208 + d *
    (-2132407738866437092436857850612998612227719168))))))))))) + d ^ 12 *
    (821467520281510287293871528983558942457856000 + d *
    (-304535057302267985581352657003912498679119872 + d *
    (108457085606760417397009964654875156908343296 + d *
    (-37028232065854743572863380524287464899870720 + d *
    (12087844775835047765884573096003964799287296 + d *
    (-3761486534535257544125253166823338614980608 + d *
    (1111568064895301115832911167471878310723584 + d *
    (-310528690069436021743926654564928148996096 + d *
    (81553668556616551199925622065365125693440 + d * (-19997867989316912356716949677238473195520
    + d * (4539177860698114914917522914714386432000 + d *
    (-943117744076610250446087374141606854656))))))))))) + d ^ 12 *
    (176661719086381599961752407129625198592 + d * (-29178078352532777032929311318733488128 + d
    * (4098033272931989704896947739090747392 + d * (-455881612692699602728174603315707904 + d *
    (32817053534950035298136903810809856 + d * (157640793146647016564700321153024 + d *
    (-431567109285752353842145856323584 + d * (58894631676406596447783753875456 + d *
    (-3363351835814399551169918402560 + d * (325971836024125181132611256320 + d *
    (-202088636594582683773635657728 + d * (60110393195007411781814452224))))))))))) + d ^ 12 *
    (-9492872606713874338955132928 + d * (685091316064784033956757504 + d *
    (38912895133578476917358592 + d * (-14739495333232417885650944 + d *
    (1361286216545060643405824 + d * (-10413062609522027921408 + d * (-6840484486221837107200 +
    d * (205748070053411553280 + d * (11971114276087660544 + d * (4643809462503079936 + d *
    (-321600884203061248 + d * (-56070653082075136))))))))))) + d ^ 12 * (1590702813216768 + d *
    (344961559822336 + d * (16128660471808 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt9 (d : ℚ) : ℚ :=
  19949944724356219173390236160655143 + d * (-843068395360025646198784923411049185 + d *
    (-1945057809350249244988124537848004919 + d * (10083130281438087810282320480638203261 + d *
    (-9455607589947025525163821593236165292 + d * (-38217655454200980740992506030204677247 + d *
    (174956798858332008726201715650479249253 + d * (-304669169795667770622937611634055991066 + d
    * (3197315700769543105011468884567730648 + d * (1380900127598962304118556546831982155156 + d
    * (-3945297377911523680296871302682142400712 + d *
    (5679027013439659363691584224812254559651))))))))))) + d ^ 12 *
    (-1140868664755675446379289146985461696736 + d * (-17075461029811805232451326885375617027438
    + d * (51531730756907169142169786421307438154673 + d *
    (-88133415968746326266960097962255018133414 + d * (85443289013753771858523522943740786668812
    + d * (22269191785802111428943331142945449372298 + d *
    (-294540126099699019781253628175100437550563 + d *
    (723412390055350038688775851871583331810713 + d *
    (-1159650477336534883090349517544044161344375 + d *
    (1270039164930266242947285028919327817393979 + d *
    (-582562084027329412262058192570734357588965 + d *
    (-1340225870827735474270195851931785293217664))))))))))) + d ^ 12 *
    (4611651686100829800359410830046151747477386 + d *
    (-8701067496639851990095228781912278597383202 + d *
    (12232473761091864075397066898692384699034241 + d *
    (-13063056180488558831239480654048048581453337 + d *
    (8739684120201992045486259994929856229723061 + d *
    (2699910246937960335529679783971463929009641 + d *
    (-21769211674222062043352875012859584206771470 + d *
    (46719773747637163657937759524210109809101815 + d *
    (-73190003669245919482700483360671111987906079 + d *
    (94529765385784818195375319722683781655196093 + d *
    (-102821080143720032465423059858192842050457548 + d *
    (90398395569640185703921943615257548830462688))))))))))) + d ^ 12 *
    (-51509053041519179661214661180850506615633138 + d *
    (-16298177084303421918693203376820598906952984 + d *
    (111397412891193846845660363362225597172562693 + d *
    (-228099047135252704957922143887475676825131550 + d *
    (357428351687462557892408906483411162000011165 + d *
    (-488471172238718252090932996526744161079343903 + d *
    (609983652562531732850503278495317539337988067 + d *
    (-711943109583585480715837987645800028062637737 + d *
    (786771935060161365660302334492892844127726366 + d *
    (-830068528162406242031851004066647394314804593 + d *
    (840796566439723398671089018177501961064596321 + d *
    (-820988331928861229135260073800220962256085673))))))))))) + d ^ 12 *
    (775090671378765060964815596861440908497121022 + d *
    (-709115941086063394839406988370962854849789961 + d *
    (629757380296759438264430053326695087640666359 + d *
    (-543598193285547965034670233042861914066472678 + d *
    (456498889520433408791898259507825733274903389 + d *
    (-373200423682185102144859089047957004614500825 + d *
    (297140552886512698070960858127476041236358964 + d *
    (-230452459789302713982426806654752493411941484 + d *
    (174099039595485316080523920329751590341436790 + d *
    (-128091649080683540690545174268954137078840251 + d *
    (91745692170190851208550257244457757041555214 + d *
    (-63934137801034658461990290153529245258970791))))))))))) + d ^ 12 *
    (43311274668997846989832297053448380144139301 + d *
    (-28490577522649096990425329677331271618684582 + d *
    (18170906773606580614182587270907083507144625 + d *
    (-11213352139976559380019275834200757097140139 + d *
    (6676382726540859947051035938615217395657765 + d *
    (-3819616080667949316190142768595139073385824 + d *
    (2086903131846715172766353674902649934269141 + d *
    (-1078211293654600921875200945273359854573551 + d *
    (517693213729073229375929407373563930097600 + d *
    (-222980390136909282175354603821580812566999 + d *
    (78590061665681126399844582113872477276589 + d *
    (-14634151844554260217344789109963273805303))))))))))) + d ^ 12 *
    (-9147721521136834150986957726455035942534 + d * (14683202756897756299850647246653588342856
    + d * (-13129815132737098465199863817284954831033 + d *
    (9671926706686919923655555290979411585155 + d * (-6398951509987066841867646387394745401020 +
    d * (3931768837878558776534965771659358920301 + d *
    (-2280626502202741288415565208394136099288 + d * (1260211308562052900831314969587452014570 +
    d * (-666956206368090868760294890304405307209 + d * (339198877519722091267894404996505369955
    + d * (-166108029197326449696440660739782798715 + d *
    (78415483610756125201871361709155537692))))))))))) + d ^ 12 *
    (-35703153714801623477889199427555638832 + d * (15678544743277758476298440228801259667 + d *
    (-6637675414688573823288959997582086758 + d * (2706984710250266269315577353535198211 + d *
    (-1062180402446908422611578332809120840 + d * (400372603419910420769255896883318857 + d *
    (-144679562607005647110877780316007928 + d * (49996176579879254246364243420855741 + d *
    (-16470583519413077076856714244319964 + d * (5153008550319352947034304642645026 + d *
    (-1523759114649351044629362711199067 + d * (423311215932281299671963029755838))))))))))) + d
    ^ 12 * (-109642413897396659000279069100331 + d * (26221975070548584594107029943814 + d *
    (-5719296225722047358445775053442 + d * (1119462603834574611288132263381 + d *
    (-192392394619958004278134873612 + d * (28127399494642045691723556056 + d *
    (-3323568873753721329195073170 + d * (287747521940162064780749468 + d *
    (-14168466942285170959007359 + d * (88856706631473148592992 + d * (-59221419285392903210304
    + d * (21751929927937566853245))))))))))) + d ^ 12 * (1173004475332221283084 + d *
    (-1682114665561849597184 + d * (410510632952006566992 + d * (-52261981647812684353 + d *
    (2990732372718413487 + d * (123175226898142803 + d * (-31115084989990919 + d *
    (1262510813206766 + d * (15421159409555 + d * (10502688480201 + d * (-635872454187 + d *
    (-175487774049))))))))))) + d ^ 12 * (5010733369 + d * (1233965012 + d * (58451716 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_9 (d : ℚ) :
    orderSevenSelectionPolynomial d 9 = selectionExpandedAt9 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 9 =
      selectionNumeratorAt9 d := by
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
      selectionNumeratorAt9
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 9 =
      selectionDenominatorAt9 d := by
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
      selectionDenominatorAt9
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt9 selectionDenominatorAt9 selectionExpandedAt9
  ring

private theorem selection_cofactor_eval_at_9 (d : ℚ) :
    (selectionCofactor d).eval 9 = selectionCofactorAt9 d := by
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
    selectionCofactorAt9
  simp
  ring

private theorem selection_factor_at_9 (d : ℚ) :
    selectionExpandedAt9 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 9 *
        selectionCofactorAt9 d := by
  unfold selectionExpandedAt9 orderSevenDualKernelPolynomial selectionCofactorAt9
  ring

theorem selectionEvalAt9 (d : ℚ) :
    Internal.SelectionEvalCertificate d 9 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_9, selection_cofactor_eval_at_9,
    selection_factor_at_9]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 9 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt9 d
#print axioms solution
