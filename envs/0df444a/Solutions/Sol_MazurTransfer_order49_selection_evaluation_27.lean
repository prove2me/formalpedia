-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_27
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:16:21.615833+00:00
-- url     : https://prove2.me/submissions/c71bbe66-0c21-49ff-b3b1-2cf403032d3c

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval5.At27. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 27

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt27 (d : ℚ) : ℚ :=
  -269088667782547981824 + d * (-30790531405759525632 + d * (47867573141842856832 + d *
    (-105780515131841089600 + d * (177002295935880250368 + d * (-116783782338179568768 + d *
    (13193697525018608064 + d * (42040129658101122624 + d * (-64370008979598515520 + d *
    (70146203371921569472 + d * (-51350398579415807040 + d * (27211467609796294656))))))))))) +
    d ^ 12 * (-10372783491147051968 + d * (-599935860872395968 + d * (7242981010690489728 + d *
    (-9178807156707715584 + d * (8127266780519833728 + d * (-6189866753374605696 + d *
    (4239976719447822208 + d * (-2611675235932549440 + d * (1479442924388034048 + d *
    (-793253637120842112 + d * (397534325123967936 + d * (-180597911692102080))))))))))) + d ^
    12 * (75110317862733504 + d * (-30039504806693952 + d * (11579341601803584 + d *
    (-3964232142278336 + d * (1128495990242880 + d * (-294533262718272 + d * (92928233603520 + d
    * (-33084237296064 + d * (9214736932032 + d * (-1665039517248 + d * (269375751744 + d *
    (-99262197312))))))))))) + d ^ 12 * (35871495744 + d * (-6339266880 + d * (332608320 + d *
    (-44428480 + d * (50264640 + d * (-10574016 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt27 (d : ℚ) : ℚ :=
  -318911027491339525440 + d * (-38725388852889789504 + d * (74484180062484609024 + d *
    (-170840539434266055936 + d * (285970308965276728128 + d * (-232229746625594513984 + d *
    (102588617429231135616 + d * (-24393073244558496128 + d * (-19643838383816777856 + d *
    (56716200729362690752 + d * (-61762738341331564672 + d * (46486168059516907520))))))))))) +
    d ^ 12 * (-30014875860460137792 + d * (15801882171083115200 + d * (-4370686799612109952 + d
    * (-1529104907577784960 + d * (2907676555680609344 + d * (-2567837466609721472 + d *
    (1866594493983167872 + d * (-1174579335657488640 + d * (676768845248777216 + d *
    (-388580944591980672 + d * (219717697875616256 + d * (-115448304070159360))))))))))) + d ^
    12 * (57248313148757824 + d * (-28413668264414784 + d * (14017484897129728 + d *
    (-6535376227965440 + d * (2862244040614336 + d * (-1209317005250752 + d * (489572303225472 +
    d * (-183108342429312 + d * (62887049113920 + d * (-20444301829504 + d * (6285547658624 + d
    * (-1684948028416))))))))))) + d ^ 12 * (346668975104 + d * (-45594667520 + d * (1976365056
    + d * (398336000 + d * (-51267584 + d * (-1333248 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt27 (d : ℚ) : ℚ :=
  4020773566922259616060092969597330582763272078345247061704704 + d *
    (-186711918183935362652050672516942394235673084824055363588325376 + d *
    (95935167107179001615911912814128225835478509804176849728700416 + d *
    (220241820099106178304432650346102335272308153131361846261448704 + d *
    (-406817902697885323717933070112488720874602606067977197281607680 + d *
    (625389581813909056284950178572858776274204611446208483012902912 + d *
    (-416917299508682990966395802180665380931874304627470599192313856 + d *
    (-303819795812104662244761667176127896791276640366231360362250240 + d *
    (1011195138616530421209874042118168075368897246173890006955589632 + d *
    (-1362853778755084397353620715728693430349982397828391151291858944 + d *
    (1169796460888996861663027070164746361703169169974158627637297152 + d *
    (-355345538484842585777940342044879983876758482064233496572067840))))))))))) + d ^ 12 *
    (-724607902458845453852831099088105086801253812212040062867079168 + d *
    (1530015326882229475420518542147336648524924287470013845712142336 + d *
    (-1753424669268139645686996677001957978700062190639032840174960640 + d *
    (1328891109356916244356852123872580437392135575626395524329897984 + d *
    (-422494385732835796493114994265041614408620508535050741917679616 + d *
    (-593327612091605658126830121115219907020829966445548931000303616 + d *
    (1348489529014606418060046597190960360541518263460057664481918976 + d *
    (-1642815458259617604034929810131858601087751423235377096661401600 + d *
    (1460227674185713426424970155652273351102448843024922457677496320 + d *
    (-935272477809432651158555008649411752549394126750926918251184128 + d *
    (287086979083537762492302165022761177591541215947119676365733888 + d *
    (279724378089447973970070091497778131578045461986665671251722240))))))))))) + d ^ 12 *
    (-640891609824651001783255922439635735185135433593261810827395072 + d *
    (763251226912044967783198108840052904658201619782958150251446272 + d *
    (-686954926921821810108993077995437432253224326642954231525146624 + d *
    (492822834280160177282479885000386585881982204662482292421689344 + d *
    (-265166607168615043731193216587160930774607792672815575241850880 + d *
    (66573823346823927654014317085087526283384090742918592763002880 + d *
    (70332012452244010524462534553381168082500265118475364027072512 + d *
    (-139869346983448628785295519118505347132301415303331479731568640 + d *
    (154391429089728207925895567064232384694537940504110193324326912 + d *
    (-133771210678052951390453185983105178115395924458264823577968640 + d *
    (97243166899773857668451965580687134668546918194254674347163648 + d *
    (-59121356439479390408740364677351364066288807004500429423247360))))))))))) + d ^ 12 *
    (27669672639158580970954476544268448624823516396874945805156352 + d *
    (-5940745208631362960701148470158714993730896116260328867627008 + d *
    (-6479378595112312508175244325460629618909048256250391104585728 + d *
    (11711945511826760861312370425802657538739271797693438544838656 + d *
    (-12294626161429511348787058060429622678129478461032436701069312 + d *
    (10436524464880846281379662394643064078314221792299703751933952 + d *
    (-7716121478833515307416927050311966668760018694764070955122688 + d *
    (5073449304290976719630799679823702381717881734007739841249280 + d *
    (-2947628868703787033102759515581949459611076271150041860145152 + d *
    (1449634365919261815684426953348329139692599572916309448458240 + d *
    (-512846937634284231065772638979688082484845900861189503320064 + d *
    (908621882134760947164406034018396784620196053494488629248))))))))))) + d ^ 12 *
    (227814515933443296688744002932475644240389924049021014638592 + d *
    (-289772329511296996435397256316493048126671367147656095727616 + d *
    (267575367852808249083138616434145929455229036922122808852480 + d *
    (-212906594654837378594685426706917937673716316963698786435072 + d *
    (154018059622416204882494136736296134483224586228624521166848 + d *
    (-103689108012064223925061039583603397805056451042543333277696 + d *
    (65712193238784929075320554736058556128852793696496592093184 + d *
    (-39406720526262709869556371242868711210507011534797299777536 + d *
    (22379529176485887712205265964165995744438058403840730333184 + d *
    (-11993089974550800556379667909016001604206538936025164546048 + d *
    (6005894668177039591481822540854832679496506191621469765632 + d *
    (-2750821522403957450706736838896892063205705839959801069568))))))))))) + d ^ 12 *
    (1094786802919735793540414473992658720916903693172728135680 + d *
    (-320561325588814831415541769053384826207754865329657872384 + d *
    (1750467856718573215169983768715558267874567104613580800 + d *
    (100146755734906933379398905181129039454962260463114256384 + d *
    (-110092229915971021005106330402035251410027040643653042176 + d *
    (88630245372047280233885901023514723948316975437026951168 + d *
    (-62081658085340078077352854558837000154002495630425718784 + d *
    (39920072351429574364342530512061183892470963791913549824 + d *
    (-24129447857639856522856401818184794850262987107255975936 + d *
    (13881039214738538035815404422432074989893076340415660032 + d *
    (-7654732771513676322106491513118142732042481821710811136 + d *
    (4064130278841622012515852087287578522552461172853702656))))))))))) + d ^ 12 *
    (-2083055275725266114686098879295304050709741812651917312 + d *
    (1032309698440870919558305676268020452234134204715106304 + d *
    (-495012622952872943246108311859814858551323887277703168 + d *
    (229688793936000659372284440793957468479173784516952064 + d *
    (-103064045288244485255939313785576227313777816988549120 + d *
    (44658868091905485982209694605100092079933395446005760 + d *
    (-18641828063770919126760569446190208995237217229078528 + d *
    (7467100434800500968817156086928896111190508379045888 + d *
    (-2852049284031583006187141592060886977748580242292736 + d *
    (1027707199599682410802784703583677368511885904707584 + d *
    (-342556596064921259076753818796124584303972944707584 + d *
    (101250169593384780613576882577416679552945507270656))))))))))) + d ^ 12 *
    (-23530175544847150319521726597484351877918425612288 + d *
    (1935297539389030462277023397651267983300219371520 + d *
    (2314148776906847768906115100728375075321637240832 + d *
    (-2124442712905700836531191774229014063221699510272 + d *
    (1285644609825463628631382827369133127801268076544 + d *
    (-661104449151598669422364706058639451737019383808 + d *
    (309149280074204982437795897900173735708484960256 + d *
    (-135207579221151371742249411196604449613882851328 + d *
    (56091311838013257637561850295468749876989788160 + d *
    (-22247238651745339291909328184060725654899130368 + d *
    (8475414795152519788330384290199518944118964224 + d *
    (-3109871187157033880631641199951067054392737792))))))))))) + d ^ 12 *
    (1100688526418610524201603632368075906138505216 + d *
    (-375979315866617841790804261691635528395390976 + d *
    (123923889728701173982562018761792147801767936 + d *
    (-39381249254475827129028103502806275174170624 + d *
    (12050095938915511993572672221360864562774016 + d *
    (-3543571794873422952032843164533522495963136 + d *
    (998899696967373417698983788183163461173248 + d *
    (-268975235064841710260500095185942428516352 + d *
    (68862304435191643536302541050895349579776 + d * (-16659264259335344971796434572755780239360
    + d * (3777519784751376673814316749034367746048 + d *
    (-794070624417147870295081966463424135168))))))))))) + d ^ 12 *
    (152357094744644852714194172763017838592 + d * (-26066613883835038140449165695149408256 + d
    * (3826611922306752956799645319258701824 + d * (-446829706905931010887888118888267776 + d *
    (33253067120185213080284254007459840 + d * (510293760619139395795075229810688 + d *
    (-596148664591993425429807966191616 + d * (90051364267395182065609077161984 + d *
    (-5876695373915501000523237818368 + d * (122473819002314722498252374016 + d *
    (-119392688922940935038576361472 + d * (50663304960695177206563864576))))))))))) + d ^ 12 *
    (-9297137651664795960649187328 + d * (752170231833470057661071360 + d *
    (33366270745329241131319296 + d * (-14917935257881721302679552 + d *
    (1371329174956975306047488 + d * (-5394349654705111826432 + d * (-6893253470543548776448 + d
    * (144097241821591109632 + d * (11613545990954418176 + d * (4990252950605529088 + d *
    (-299681104235855872 + d * (-55241113963331584))))))))))) + d ^ 12 * (1614437689589760 + d *
    (345219383689216 + d * (16128754843648 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt27 (d : ℚ) : ℚ :=
  103511570158902000339666743062730540039049526943733 + d *
    (-4795118585525565385389540998114128457698784703663189 + d *
    (1908184600862109055291524164603966168029193015077245 + d *
    (6961183592051674292598957994972318931093912619164349 + d *
    (-10902633193088208075046627164037625084969241070581792 + d *
    (13787589797674689452106459053318156549040244941736659 + d *
    (-5433683361985332850963743277163662399123184516693349 + d *
    (-13755185579566403795796280462075752825194396927048940 + d *
    (28042814010056052974049529584782438307553529352650460 + d *
    (-29411355428947364329527255999649867388715279555875882 + d *
    (17314875522999947916650771387614816456740025124924762 + d *
    (5268633713439824460065310966997500584742030614695193))))))))))) + d ^ 12 *
    (-27259151840723539453597368854244362953142927048245472 + d *
    (37039219590710555573883675964606018466536055081835586 + d *
    (-31889979146983395277425568901217152455116629598302877 + d *
    (15411578496533819773964461943578924576766887493250078 + d *
    (5661339839325645733310834507379617435950035547684990 + d *
    (-23134174668722601089395889796290489272916815121188640 + d *
    (31438890125368758521502395291014817498912667578734633 + d *
    (-29794488483025443704156503074141874715373068708386719 + d *
    (20758851167542815873233272984189648339349223146004335 + d *
    (-8447621544212361500237215975413542951930006253138377 + d *
    (-2927924372293035147978587148183754677163429776343801 + d *
    (10568337214430618936663250092023338669881419868022266))))))))))) + d ^ 12 *
    (-13653537078921238930324727875863369053124652161991748 + d *
    (12862367610039713735058602393783234234834545924736696 + d *
    (-9652189896851105190615967812808063768824809811719157 + d *
    (5614579900683075029816602713678908529494255408538005 + d *
    (-1969465836623409631214136847297690213640556188579373 + d *
    (-639890102964868332456832274567744546331661911618117 + d *
    (2073376684170007301187004223159424339322727127895162 + d *
    (-2516881887042978567575842261566124324821195353732707 + d *
    (2302444274126418572248132881219293996564512955274625 + d *
    (-1763160891424277860640891701921546036898635757623681 + d *
    (1151448183055100015063832896910941093379327943079176 + d *
    (-618671072573918114921736187720879911569514929530956))))))))))) + d ^ 12 *
    (229244212980969995853535863508409206361912763866710 + d *
    (12391080158573652630285295495639670662814422094292 + d *
    (-133619497980913618530129686241211806437440610674707 + d *
    (171873598401881142045410990717455016102782105128040 + d *
    (-161826072647047626628727264042874623708546413983671 + d *
    (129806570818082918548056689747274927669485622903501 + d *
    (-92786015747394092705290806805346738408467031674595 + d *
    (59850913940829625012202652165532258010492853204591 + d *
    (-34569256331181536210560224721610150679270842029656 + d *
    (17223932067531511044523752117772935284768504834403 + d *
    (-6507248455836066368004457947985762268784580293673 + d *
    (626710002436948945982676418671632217868808622377))))))))))) + d ^ 12 *
    (2090603785751476497838873942684746016291630496026 + d *
    (-2950814248415331494537019068107534927209370698083 + d *
    (2855582883830333647128622734921325837104626106611 + d *
    (-2363587103918702387922611350387750337850476648058 + d *
    (1783324222486163681681045490588690402289320253043 + d *
    (-1260874886412042048878315538055461446748526726795 + d *
    (847709548473151535850767097608950839006879143168 + d *
    (-546673737159450003880882228057623026426631572030 + d *
    (340032143091491735116020840880276803155337606720 + d *
    (-204750686837095061667017536252189492796432466699 + d *
    (119657744515474164129744734863485012907631497264 + d *
    (-67985443237191003339207701893023332333021728245))))))))))) + d ^ 12 *
    (37596540818779634541636844707848411887587288863 + d *
    (-20250969746186649655044371486143044126757161960 + d *
    (10628538474585853659550760673672425767883468979 + d *
    (-5435896998495471984912229914144947775465256773 + d *
    (2708718157415923174943540713898024094396861639 + d *
    (-1314508472988420452646323129356142795296393214 + d *
    (620814431771449085811444949072089345506249773 + d *
    (-285041048220062474505990205446673296028801865 + d *
    (127046784613173144849663093822649678209488030 + d *
    (-54858573424927541579881050323452571358192425 + d *
    (22882394744146380739477534383274476300107477 + d *
    (-9181486342841492102136527709685291886652677))))))))))) + d ^ 12 *
    (3521156588811937568193093781720880897143856 + d *
    (-1277174495056260060736015858805210290489634 + d *
    (429940303748367962485068579638566239129515 + d *
    (-129138182554552811961707107287973630517129 + d *
    (31071042394411769215166187468199204727400 + d * (-3241343673775666336360666026819240886313
    + d * (-2550218043840551295331206473123716644798 + d *
    (2535397519769472767462139784781570160862 + d * (-1574145926931882225123244696300860579161 +
    d * (821985153206134013023920541680554999981 + d * (-388891813533615477946731044769249420363
    + d * (171787732733213336825184575530740467258))))))))))) + d ^ 12 *
    (-71916677217545720402561449303531247606 + d * (28767662047399239676036431333073211023 + d *
    (-11047561393987193349690792959119804510 + d * (4084075601577185756028400324322657841 + d *
    (-1455546297906113002896012283080015782 + d * (500406645211686284385785109566499001 + d *
    (-165921938631363324352548501495838144 + d * (53005452242602078059928323903792717 + d *
    (-16283714801846448529111837193834584 + d * (4798218655295213417167279799619556 + d *
    (-1351957422571024444645429689766703 + d * (362903098228814524787109651334862))))))))))) + d
    ^ 12 * (-92322946905187091387965976904793 + d * (22078121087778494902380050021448 + d *
    (-4899355694654249253354799137598 + d * (989789657714628335373645440993 + d *
    (-177202274757881898302394342940 + d * (27043577528034907251607430258 + d *
    (-3302333989249224620938446930 + d * (281456260927373787493695374 + d *
    (-9197331943273286707496875 + d * (-1227484909348743076399886 + d *
    (124058680174663276927110 + d * (11559659177167613166861))))))))))) + d ^ 12 *
    (89238735096644939110 + d * (-1429516313736413699672 + d * (395639189149647915684 + d *
    (-52805047050385871203 + d * (3030838355347377999 + d * (132878532275685621 + d *
    (-31022757747414491 + d * (1100637402704768 + d * (13654914078215 + d * (11586919455711 + d
    * (-563504850213 + d * (-172766390013))))))))))) + d ^ 12 * (5090778973 + d * (1234879412 +
    d * (58452202 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_27 (d : ℚ) :
    orderSevenSelectionPolynomial d 27 = selectionExpandedAt27 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 27 =
      selectionNumeratorAt27 d := by
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
      selectionNumeratorAt27
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 27 =
      selectionDenominatorAt27 d := by
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
      selectionDenominatorAt27
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt27 selectionDenominatorAt27 selectionExpandedAt27
  ring

private theorem selection_cofactor_eval_at_27 (d : ℚ) :
    (selectionCofactor d).eval 27 = selectionCofactorAt27 d := by
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
    selectionCofactorAt27
  simp
  ring

private theorem selection_factor_at_27 (d : ℚ) :
    selectionExpandedAt27 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 27 *
        selectionCofactorAt27 d := by
  unfold selectionExpandedAt27 orderSevenDualKernelPolynomial selectionCofactorAt27
  ring

theorem selectionEvalAt27 (d : ℚ) :
    Internal.SelectionEvalCertificate d 27 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_27, selection_cofactor_eval_at_27,
    selection_factor_at_27]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 27 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt27 d
#print axioms solution
