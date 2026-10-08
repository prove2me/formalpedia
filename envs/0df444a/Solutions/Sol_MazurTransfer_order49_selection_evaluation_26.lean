-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_26
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:10:21.716909+00:00
-- url     : https://prove2.me/submissions/2afd4ad4-67f3-40eb-9add-4d8a8fb20093

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval5.At26. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 26

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt26 (d : ℚ) : ℚ :=
  -171325252120233476096 + d * (-20634854878579568640 + d * (33661326966249635328 + d *
    (-74308627414781114432 + d * (122162536714846376064 + d * (-80168766501575907840 + d *
    (7182535706334572736 + d * (33251205132563604096 + d * (-50151349923936506496 + d *
    (53967957989761454656 + d * (-39405086122094642112 + d * (20678270646496529088))))))))))) +
    d ^ 12 * (-7320677239332366784 + d * (-1458141750578640192 + d * (6691606588894347648 + d *
    (-8138124370849319232 + d * (7176655048074571392 + d * (-5477391763962169152 + d *
    (3765251667397014400 + d * (-2333558256869801856 + d * (1331960797373748672 + d *
    (-718587351042592704 + d * (362034318575380224 + d * (-165648522705317376))))))))))) + d ^
    12 * (69496393466717376 + d * (-27965467165754304 + d * (10801187241907968 + d *
    (-3707018030904512 + d * (1063644582294144 + d * (-281067061956672 + d * (89051976573504 + d
    * (-31615258497792 + d * (8827581267072 + d * (-1615918501632 + d * (266586781824 + d *
    (-97378444032))))))))))) + d ^ 12 * (35018682240 + d * (-6231950016 + d * (339075648 + d *
    (-46578112 + d * (50121792 + d * (-10576320 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt26 (d : ℚ) : ℚ :=
  -203046063181929676800 + d * (-25991419223724165120 + d * (52152862086507972608 + d *
    (-119702517984909769728 + d * (198415798881358761984 + d * (-161882995701562093568 + d *
    (71285370107158411264 + d * (-14582470698818212352 + d * (-18353622825863294464 + d *
    (45316257204631639936 + d * (-48543078695933540992 + d * (36574311582711156672))))))))))) +
    d ^ 12 * (-23518599225492062208 + d * (12137784272487822976 + d * (-3046530782378259712 + d
    * (-1624031951757281856 + d * (2684077797646207936 + d * (-2341778278902993856 + d *
    (1696580839850241728 + d * (-1071187191098337216 + d * (622820719613419776 + d *
    (-360046393652169536 + d * (204524462758914176 + d * (-108418082565311616))))))))))) + d ^
    12 * (54445926778232256 + d * (-27278328139867456 + d * (13528780454688896 + d *
    (-6349641659331200 + d * (2806062477259840 + d * (-1194126057983552 + d * (485361422803776 +
    d * (-182329412861120 + d * (63030431115840 + d * (-20600071230848 + d * (6333835420544 + d
    * (-1691660399616))))))))))) + d ^ 12 * (346737779200 + d * (-45525049856 + d * (1977928704
    + d * (396945408 + d * (-51407872 + d * (-1334272 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt26 (d : ℚ) : ℚ :=
  1037634128977225190307236862186608792927563956493160164622336 + d *
    (-48143267333244371407175553156145100207729964256100725041397760 + d *
    (23519867806902969012527654011273018935637048536733653739241472 + d *
    (61537333249488265166062928993676303982278172682930520238063616 + d *
    (-114924992107314853068788144589983586938871972370609887990775808 + d *
    (173560300539090390756139851985004400417075987622333569126367232 + d *
    (-108560210079517749014497082908728998014084834405163087217819648 + d *
    (-104264402068580810429539195836694997877632662981021930216226816 + d *
    (315358938333886352731521175433911971096211944053962241438908416 + d *
    (-417872110071546488717401933647018714311627961745606341792890880 + d *
    (347298561386176779722432261505215135756264262976548303638626304 + d *
    (-80419981806929812569320970987919560356605836301326346422321152))))))))))) + d ^ 12 *
    (-269613204506249321448098537025163926780779261639172615400587264 + d *
    (528614511659971286876926400597571687298434057778241740630392832 + d *
    (-590551960222289816026912392056432172802213426251280467113279488 + d *
    (429751251972840599120315227695707835875346834752509736225341440 + d *
    (-103462657333639953407189735691221917004991307409570385998643200 + d *
    (-258361955248453187445838367773093484642471239315074871265853440 + d *
    (523992483534958581825420339099012836906759462118307590158417920 + d *
    (-619138726565378396041627036281034489508603842993631852890947584 + d *
    (536553946623836161712789454971779449010454698533715281694949376 + d *
    (-326355076791315663968896635814302255669677772659818106553892864 + d *
    (71569062136285004339618584301696489737348490618724144311173120 + d *
    (148919992098768969407791397546232667080819756455218195398656000))))))))))) + d ^ 12 *
    (-286077586647057767798634898610042884905479751703648472812748800 + d *
    (326506664418620555725316541928484597959936360571426893007159296 + d *
    (-286459715300267865202604476306739486106073108499589730290892800 + d *
    (199053352115357246358604877315463999487580556902622489413156864 + d *
    (-99284378486025330303677548588179801751566986277970449828675584 + d *
    (13486105816356768739871485558596552934558472054724036681007104 + d *
    (44521935155722264209357583972751779431043484696700926541430784 + d *
    (-72472686538453318132802986272839281096235745358307162691469312 + d *
    (75974491202823831699714566516516113918031841853481182518837248 + d *
    (-64002870021359319310383047432964040284238353705150628191797248 + d *
    (45301431944430278055267490720981521698799617514510605559005184 + d *
    (-26410968108765071440853651987914877341953539571966324517634048))))))))))) + d ^ 12 *
    (11100502300355403931171180846725808634130095936893564501622784 + d *
    (-718255865630015620084890760509518466425257463461879650975744 + d *
    (-5016731665086141609887571837368149760512440534844263561691136 + d *
    (7194913944827725013101047731524224066141996892223170884927488 + d *
    (-7100162594830022285203490933671606913516026378852896236634112 + d *
    (5846648249650460389617056774210807902540997363377651316162560 + d *
    (-4228962969130388527253892331522407834226140862174848685703168 + d *
    (2717114796186695330293722282708309589908345370387279066955776 + d *
    (-1524929434933757188012884894603440041546930177107234092482560 + d *
    (697751826444498089796215452980010918525154574478160532340736 + d *
    (-190009020711928276040689786012126726321253254420904469594112 + d *
    (-78653317339278848653525799667730449489116732713195710447616))))))))))) + d ^ 12 *
    (189563641319652617690120261594049312773083272073748731658240 + d *
    (-208995602148596375317796256019706578773594404044910555299840 + d *
    (183727952502881357778937122638796883889060560867238531301376 + d *
    (-142846673741770111562622345679892008966095698953939644579840 + d *
    (102046097056205533068862479847208984027049234808802683125760 + d *
    (-68177503561505045811164506450396488945595000544710080069632 + d *
    (42970524761735728631674286151414974875683252296052504264704 + d *
    (-25636251917108959601574429981735543778627524657249457012736 + d *
    (14464716914343949170715298157986179560800468029138509496320 + d *
    (-7674032683789485933118254303287250938996038538523524726784 + d *
    (3776272024807828862376753712961844449769536519059917242368 + d *
    (-1671772294321205278181264552037071201004579979453941415936))))))))))) + d ^ 12 *
    (614544822317276977382261692697272535586876088586745151488 + d *
    (-132479460407256288310110508941213677518119714341833408512 + d *
    (-55055618830017125045171765263077186536122590875336310784 + d *
    (104787737767548492618217831456871200144689948137672671232 + d *
    (-98431759719285746614747633167616771974934761429935587328 + d *
    (75106365141329720944725187744196663530940241180197912576 + d *
    (-51338164018415767655545705314184440829356993135388917760 + d *
    (32611152817857008310063388102281548025662999623918682112 + d *
    (-19594319306044337201093454252748583895622209279903399936 + d *
    (11245001279420452508276127149252997285242067732610678784 + d *
    (-6199639608210547785626500050927268571138146715928625152 + d *
    (3295324800191896563926673448003061427613365148542566400))))))))))) + d ^ 12 *
    (-1692383660286535478056600250504173141725181850021789696 + d *
    (840801729251151006203088994791305586065039500948537344 + d *
    (-404280724634251470042926262547644842099128637189521408 + d *
    (188096321852211151460800883915165085942884539821719552 + d *
    (-84606098114477307320713419143028286834565458421612544 + d *
    (36728686211509595170731984977763490449559188068892672 + d *
    (-15344791679283794753181404473718186358714924873023488 + d *
    (6141843532383454607480140377553653485794053796397056 + d *
    (-2337811652123521885643947603219065034759961596919808 + d *
    (835507966575336009358941748018815486158696555479040 + d *
    (-273589700864909659826324396349082169609727732613120 + d *
    (77607753132370606678683024940971835681954819211264))))))))))) + d ^ 12 *
    (-15846332327852375051905200626996986642160803381248 + d *
    (-402486124272801028368193849555090290466513223680 + d *
    (2964729654746518787378636225421570534868202029056 + d *
    (-2281889727905203387982751833340872477991739588608 + d *
    (1314065953043289634358686556558167324519035568128 + d *
    (-661781168574732715041007533609289370206891409408 + d *
    (306453213239148021865704317371354218050993782784 + d *
    (-133436597235740429665332722276026003905961263104 + d *
    (55275085230029273751659450761342591475371212800 + d *
    (-21929669021996635401462944129791505209353306112 + d *
    (8365847139863683332613823957552284260811931648 + d *
    (-3075922262756287640975136776029644579706241024))))))))))) + d ^ 12 *
    (1091322560944543988249463785791809256321712128 + d *
    (-373764577953136847530873001348484679028441088 + d *
    (123528436965206733378828188669708522606821376 + d *
    (-39361184441733299405635056661285787377598464 + d *
    (12075002358371969570374264155230074354008064 + d *
    (-3559342220181507990913881421190533978521600 + d *
    (1005445443200364846992114935903946684235776 + d *
    (-271205684533820978481960654312813313130496 + d *
    (69523024725066655618458588748899310370816 + d * (-16832312514215097549598753850017371914240
    + d * (3817530050104686211851351030172250275840 + d *
    (-802113302071982642424084905994552868864))))))))))) + d ^ 12 *
    (153719700128623414505999018704245882880 + d * (-26250098874091756263834081644175949824 + d
    * (3843811859395875871180539519756140544 + d * (-447493918103158356943728584803745792 + d *
    (33204072854881640256714759520387072 + d * (499952703297675666253677935460352 + d *
    (-588231565850349826331849200500736 + d * (88362752740765450141672898297856 + d *
    (-5726211908649354462861883867136 + d * (132235083756784499972308467712 + d *
    (-123972768776578910333249257472 + d * (51197937137206985830620463104))))))))))) + d ^ 12 *
    (-9307825220663134035443974144 + d * (748323712746374854830194688 + d *
    (33669362439616673528414208 + d * (-14906602777241460827750400 + d *
    (1370830797302934118596608 + d * (-5680529127057836212224 + d * (-6891007766294875602944 + d
    * (147492799468863750144 + d * (11632552313992511488 + d * (4970995173996888064 + d *
    (-300898890547724288 + d * (-55287199469928448))))))))))) + d ^ 12 * (1613119085346816 + d *
    (345205060141056 + d * (16128749600768 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt26 (d : ℚ) : ℚ :=
  29833357762182406495111409581263512092134852263936 + d *
    (-1380700945209364667372362739783444907961489052139520 + d *
    (508238872495168922151603974936596682064504743264256 + d *
    (2150518538113111683738925145145896749982576732831744 + d *
    (-3404934113716762382436083280891290412970750492581888 + d *
    (4224154227910290472049498502275466657027817100725248 + d *
    (-1417116539120808831100173216735579137181178993515520 + d *
    (-4858498275142296309108072220972342031684335951931392 + d *
    (9559541871920172334955127910400938945936325857942152 + d *
    (-9880056149615642554425933063128992268433912159440873 + d *
    (5450146580222597809517399170688384681882558255969870 + d *
    (2664607986154240439322200980445906427619604397054179))))))))))) + d ^ 12 *
    (-10506842402477293687754430951481652755193452823847735 + d *
    (13877369648840741844723166314670899634030540573978484 + d *
    (-11648607665330039624226925046082093996964011248746617 + d *
    (5084345059054650290255803315730970543603389080628846 + d *
    (3213845539406234287061012722737414140499271790433398 + d *
    (-10033012697689508286624793786828812597407522478608810 + d *
    (13146795828984172743665938420868360963240767039988318 + d *
    (-12189469575256979614697172599716778523364310983913088 + d *
    (8180596577469872902131820699168108124566603872392382 + d *
    (-2839032589432352248303897076361806030876036176230231 + d *
    (-2049898749500481998215742993900183475079927941282850 + d *
    (5280295770768355333474431881125030809735424861858760))))))))))) + d ^ 12 *
    (-6484505998514022836529846977918736976058342908671847 + d *
    (5957343882171539472384841161809193827722891110517380 + d *
    (-4354211995695483462708470866993592186478234362182043 + d *
    (2400619009741875208373058047187450620184866693547916 + d *
    (-659417672424165227785700819489678486276134909572603 + d *
    (-568746489126967437736276239274154168748191766938033 + d *
    (1219255550055199276368914784329974034208441566862625 + d *
    (-1384685041595325244313868047782338653058903752150724 + d *
    (1229626147923814824631469984632673077512416489542191 + d *
    (-920187282237194718920743718245237829832046548778977 + d *
    (583205801662582358462981282902451411173169569599046 + d *
    (-294953724641262721790879188061900979604883626192859))))))))))) + d ^ 12 *
    (87347647852585679239685806813021956600239108387966 + d *
    (38658618267813503197823032909100927719620140980245 + d *
    (-98684980959769979874583874132998386540562509435262 + d *
    (113589875713112513796148141038788458874865849916535 + d *
    (-102647026536732672924033572772582854247316463936942 + d *
    (80490351574251001169454982187702591116151590970659 + d *
    (-56531857727095347140803518427621686828788469013849 + d *
    (35758423935827266503354392945089706486352835493073 + d *
    (-20039138414910659461392518621239366711895651344881 + d *
    (9380283360759234889905445727832995469047327686431 + d *
    (-2891699001103329016824637235343731705487285764039 + d *
    (-576125055661766265218367334201963983487925621003))))))))))) + d ^ 12 *
    (2081333625389113328247811089362050451292179308647 + d *
    (-2446820210136750596762786520901767084136633922135 + d *
    (2239765997778080237177752349461968489024351882316 + d *
    (-1810704518305111998773562070455304949595767010023 + d *
    (1351743695006952427041412865511584377568221716841 + d *
    (-951816660858783705762812914103159766391712155174 + d *
    (639680981810480856415322617649446071154474084645 + d *
    (-413315141296721349073467477718689032378794556846 + d *
    (257966409487899721805893312931909109575383893441 + d *
    (-156026447772826666322371516573066218901503123944 + d *
    (91652000694738191749001045613234969404263174813 + d *
    (-52365601978810287672963957672373756171977434375))))))))))) + d ^ 12 *
    (29129803735885906601387069965924023458217488808 + d *
    (-15786008295640104136844190371321416527500355171 + d *
    (8336251004941610836945716950169876803505675896 + d *
    (-4289782680343386134923619584073642027849694781 + d *
    (2150582647800287709747610694383164369603142316 + d *
    (-1049809386293541875051566778855945578856942153 + d *
    (498598382377646937749283791066153766971787267 + d *
    (-230132459026568803408551700336614443688265187 + d *
    (103060550281367015216601972124703915343278145 + d *
    (-44680695542208660579408645228905604488824046 + d *
    (18692902021702670508242906178561190906722625 + d *
    (-7511420113237740793507238020979038253239068))))))))))) + d ^ 12 *
    (2877922970841697574254760192587467054280680 + d *
    (-1038570981667780126266701678575071990431215 + d *
    (345079801383895710733980168608747600283173 + d *
    (-100391204905136376481388306471550294996508 + d *
    (21891979646284318526560394934301846960542 + d * (-529035247706154568240802384918627574047 +
    d * (-3264708132035778804822796551730723467700 + d *
    (2687599211068703360709534414942638709136 + d * (-1590317221069358475792568249857726227590 +
    d * (814779752631560267473293012058929009247 + d * (-382314607797607464597150582154190457361
    + d * (168351018476978699006756357126177208421))))))))))) + d ^ 12 *
    (-70450146975993596653019912235700395962 + d * (28215203590966666885864794278098178462 + d *
    (-10859116543458663270007154251633805884 + d * (4025590204190640849352859313951283602 + d *
    (-1439189652023399861457589941570878298 + d * (496404997743262067516832021915587115 + d *
    (-165132943035754876794271309794104118 + d * (52918854798133494428142487527963944 + d *
    (-16304793218679443792542884985881337 + d * (4817356065563962239399361598177106 + d *
    (-1360588698870730734764892773699113 + d * (365927391785758589588264674610455))))))))))) + d
    ^ 12 * (-93209083883755813306376795581188 + d * (22297459989222558483442070254141 + d *
    (-4944557199070415172851252365796 + d * (997277902303059383722762639970 + d *
    (-178130943361627387328150979176 + d * (27115974357899582804627454679 + d *
    (-3304068061933218579871931442 + d * (281658517913634169891184264 + d *
    (-9439542617108435133961959 + d * (-1156980966151898384545711 + d *
    (113793567065325809413925 + d * (12150919325496102920363))))))))))) + d ^ 12 *
    (149762144276053885523 + d * (-1443765443153689113990 + d * (396450422512817547750 + d *
    (-52771831621887072569 + d * (3028783418389082844 + d * (132320081549645922 + d *
    (-31029899943346662 + d * (1109541833661340 + d * (13750403027376 + d * (11526649158459 + d
    * (-567525348867 + d * (-172917578015))))))))))) + d ^ 12 * (5086331995 + d * (1234828612 +
    d * (58452175 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_26 (d : ℚ) :
    orderSevenSelectionPolynomial d 26 = selectionExpandedAt26 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 26 =
      selectionNumeratorAt26 d := by
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
      selectionNumeratorAt26
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 26 =
      selectionDenominatorAt26 d := by
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
      selectionDenominatorAt26
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt26 selectionDenominatorAt26 selectionExpandedAt26
  ring

private theorem selection_cofactor_eval_at_26 (d : ℚ) :
    (selectionCofactor d).eval 26 = selectionCofactorAt26 d := by
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
    selectionCofactorAt26
  simp
  ring

private theorem selection_factor_at_26 (d : ℚ) :
    selectionExpandedAt26 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 26 *
        selectionCofactorAt26 d := by
  unfold selectionExpandedAt26 orderSevenDualKernelPolynomial selectionCofactorAt26
  ring

theorem selectionEvalAt26 (d : ℚ) :
    Internal.SelectionEvalCertificate d 26 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_26, selection_cofactor_eval_at_26,
    selection_factor_at_26]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 26 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt26 d
#print axioms solution
