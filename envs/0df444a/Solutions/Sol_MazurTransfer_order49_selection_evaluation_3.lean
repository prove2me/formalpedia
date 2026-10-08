-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:21:20.580628+00:00
-- url     : https://prove2.me/submissions/58641840-a777-4ce7-b740-6fb780003661

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval0.At3. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 3

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt3 (d : ℚ) : ℚ :=
  -1259712000 + d * (-5052844800 + d * (28348133760 + d * (-12800609344 + d * (-329040336384 + d
    * (1564013769600 + d * (-3300230225472 + d * (-687775465920 + d * (33076702069440 + d *
    (-148731022068032 + d * (448137319376832 + d * (-1074004853981184))))))))))) + d ^ 12 *
    (2178003250348096 + d * (-3856745464169664 + d * (6074974956091776 + d * (-8613207541289472
    + d * (11078112557403264 + d * (-12989118885654912 + d * (13921740599419264 + d *
    (-13655013133948224 + d * (12252453965893632 + d * (-10036931612670336 + d *
    (7477983508701120 + d * (-5040712229378496))))))))))) + d ^ 12 * (3053511786029760 + d *
    (-1648084301204544 + d * (785308050640704 + d * (-329573913477824 + d * (124667255416896 + d
    * (-45488354704704 + d * (17173892265408 + d * (-6452396184000 + d * (2121332017344 + d *
    (-569364483648 + d * (145078541376 + d * (-47558584896))))))))))) + d ^ 12 * (16231918656 +
    d * (-3745220928 + d * (487824192 + d * (-96019648 + d * (46836288 + d * (-10629312 + d *
    (326592 + d * (122496 + d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt3 (d : ℚ) : ℚ :=
  -1490239296 + d * (-7090514496 + d * (49400188416 + d * (-93510071040 + d * (-163166157504 + d
    * (1724451511744 + d * (-5920141909632 + d * (11186854833280 + d * (-5129611861632 + d *
    (-49097660877632 + d * (227046528057728 + d * (-645522834434560))))))))))) + d ^ 12 *
    (1439775648046272 + d * (-2708152422573376 + d * (4437446861576576 + d * (-6451320995075200
    + d * (8430429878084672 + d * (-10017085934840960 + d * (10957208753597824 + d *
    (-11190027711039744 + d * (10823203624638464 + d * (-10023798834497664 + d *
    (8923005750107648 + d * (-7602961063438336))))))))))) + d ^ 12 * (6145188099077440 + d *
    (-4667459704036416 + d * (3306724919536384 + d * (-2172367108143104 + d * (1315589303177152
    + d * (-729651445660864 + d * (368108743109760 + d * (-167683658552448 + d * (68237099364672
    + d * (-24362209961344 + d * (7413349195136 + d * (-1841608023040))))))))))) + d ^ 12 *
    (349038703616 + d * (-43914234368 + d * (2013892608 + d * (364961792 + d * (-54634496 + d *
    (-1357824 + d * (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt3 (d : ℚ) : ℚ :=
  377892808223075249335566336 + d * (-588793318990721722154483712 + d *
    (-343864084676337629276519006208 + d * (-646454888333400388078781595648 + d *
    (23886801655636846769119090704384 + d * (-70681171940754663955228978839552 + d *
    (-508271364068036251625647318499328 + d * (4762029633299196456060857874382848 + d *
    (-12382985625696895298540513789214720 + d * (-41630831137290047582210096508698624 + d *
    (481884548088181084603487099834335232 + d *
    (-1863476027759179172689301656410783744))))))))))) + d ^ 12 *
    (1977867227619444246047141173829042176 + d * (18395654721791176173102090770226872320 + d *
    (-127448781102422556036947271142917799936 + d * (431050461964970493313736988663143727104 + d
    * (-669324103543183550986054649106137088000 + d * (-1597660467691874924311415026861994672128
    + d * (15706403925779910680141057401083916189696 + d *
    (-63552263573647958278449857262760090402816 + d *
    (165339647371760785587209005104303500165120 + d *
    (-227456812164025838270211009102796476383232 + d *
    (-360400464220381151595556790226963158794240 + d *
    (3725845140691180941357783761974380208062464))))))))))) + d ^ 12 *
    (-15182356252065302617895962131145181021339648 + d *
    (43966124444286391874945998885698468714119168 + d *
    (-95850154648850358680444937728441903545581568 + d *
    (136397872635393792042918552436678250483679232 + d *
    (25276854979960564196836707512486564592353280 + d *
    (-1031939756675577892392650616629012694146220032 + d *
    (4621657781385446167616000072141629315855679488 + d *
    (-14857500546490304171901461686901415708556787712 + d *
    (40200802388315658459580465477558683454980227072 + d *
    (-96561882240935450654268535847672545696183746560 + d *
    (211070589102620879690877360983483803705725419520 + d *
    (-425526561000344322583164895765597459675400896512))))))))))) + d ^ 12 *
    (797268619085100461965171326371985970406906920960 + d *
    (-1393670125793389829369575762000524985243644461056 + d *
    (2275006386796346414981132369143782845670001999872 + d *
    (-3459710914155367948606587453820898395118605959168 + d *
    (4866870927290825033411822085115878555008172032000 + d *
    (-6233966874368600031096039381486735366179426402304 + d *
    (7013677737300620636729081530329089850341418860544 + d *
    (-6261646959427274523283944988489221392081947983872 + d *
    (2536100186567830038482511649875005815315424083968 + d *
    (6162041193035429500741940248930508798929098768384 + d *
    (-22376003069733197575415054235200209805737616736256 + d *
    (49076777450423839465746795758002856461750564814848))))))))))) + d ^ 12 *
    (-89423517158027091311286999455594668673512227209216 + d *
    (146398778962899132076974308504867988211170439856128 + d *
    (-222340923506420357065454599881238646031488847183872 + d *
    (318422829394533826473305730018702437089746743459840 + d *
    (-434150510440476968055093585508220776534807490330624 + d *
    (566971429960802443855555025036337333605623610736640 + d *
    (-712084738026615061321721748216287290631757554515968 + d *
    (862530332697866148430881341837446527959519962071040 + d *
    (-1009599508967490900491816867115130507025740928122880 + d *
    (1143559990209526724368707267557189185772299729502208 + d *
    (-1254629777251858151633731656055936535195870979948544 + d *
    (1334078723706897780126671563201737905678761048932352))))))))))) + d ^ 12 *
    (-1375297058563849636381949798280100987251193553616896 + d *
    (1374657868822272767999793346801853100079885706067968 + d *
    (-1332022519249517829535748074413222242821736221900800 + d *
    (1250793008664593823750336088444452956986975189729280 + d *
    (-1137493516695804480593406277568542072181771394875392 + d *
    (1000948144504739952825332282313732735810658408595456 + d *
    (-851193726839557007275919922910267604854631618576384 + d *
    (698309058102705288982817672874980357884023446700032 + d *
    (-551346006251660496836036395790853294114841475678208 + d *
    (417514834615616636162199337729453501152020785790976 + d *
    (-301715841268400001670196963774174563293237470822400 + d *
    (206438066023611823376266185879034794878354582142976))))))))))) + d ^ 12 *
    (-131980083085404368689588480254713356515971283812352 + d *
    (76900984985654399936628909843089215010470436536320 + d *
    (-38588368215054636552414101048511664012719727050752 + d *
    (13834227120154347496630603819892461717023195398144 + d *
    (666769586462276003374594888708741168930038743040 + d *
    (-7948173401100680859903162338602274379345484054528 + d *
    (10548377838154346840306976908571600368832235962368 + d *
    (-10420878206932472596858042867894762078460676145152 + d *
    (8947879853882020448662315918847588735629136756736 + d *
    (-7019878473088141938625363000150713454356830617600 + d *
    (5145878821908757990762140328414387648930317336576 + d *
    (-3566701290067119302084169488873739451001227182080))))))))))) + d ^ 12 *
    (2353802863250070337591975312283656509952211550208 + d *
    (-1485409025078259357934544855548734454790732644352 + d *
    (898871640279135413698647802203011861870091173888 + d *
    (-522514690777587182781989054039897119452855009280 + d *
    (292098207277476303511023029532447808323847454720 + d *
    (-157128889528972982938915012465604133889565261824 + d *
    (81354684729532086566216202187806118199311466496 + d *
    (-40539298851282305386630749363661111664254386176 + d *
    (19435144111327584367890098793175144188924657664 + d *
    (-8959021028698088978690452273510458589043752960 + d *
    (3967660155022259699179787943823671680600113152 + d *
    (-1686339072953105384968739728012589701330632704))))))))))) + d ^ 12 *
    (686938295872042196732314288993164594411470848 + d *
    (-267768879003340213991738956578455367108788224 + d *
    (99688943915279952468569265547367960873533440 + d *
    (-35367375768208524157881035353516486216122368 + d *
    (11925517623178278168523677850905489905287168 + d *
    (-3809896240064039798329982483685542865141760 + d *
    (1148958531112346269142680211638428990177280 + d *
    (-325639345424561315018878156177473221427200 + d *
    (86278848115855045413077794740921808453632 + d * (-21231443379280834175861822503006547476480
    + d * (4812920553427549109225729971473854496768 + d *
    (-994404377660455072510003357408372457472))))))))))) + d ^ 12 *
    (184545760182457462892349380733457137664 + d * (-30109990559657229160435056833132756992 + d
    * (4169937649945591265544847450410844160 + d * (-457706691957268579751207577955336192 + d *
    (32915557719360251139710684575563776 + d * (-39863789804152111113378086780928 + d *
    (-366550705231560155562511240003584 + d * (48174379361610314940676175298560 + d *
    (-2615173481348137759210990206976 + d * (406600054321491105813300772864 + d *
    (-229807055668534087877481988096 + d * (63179923634388470637605683200))))))))))) + d ^ 12 *
    (-9559361138738234872186798080 + d * (663732078184414210352218112 + d *
    (40802017398067383594123264 + d * (-14692168917752804287447040 + d *
    (1357429922814173858496512 + d * (-12023663987007120736256 + d * (-6817084970941793173504 +
    d * (226548129981219733504 + d * (12097576396440731648 + d * (4528420766086070272 + d *
    (-328907301691850752 + d * (-56347166121656320))))))))))) + d ^ 12 * (1582791187759104 + d *
    (344875618533376 + d * (16128629014528 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt3 (d : ℚ) : ℚ :=
  4277586534800942637 + d * (-2209600564560960453 + d * (-3903125432696549972019 + d *
    (-11374910125819211479203 + d * (266239463588119608341184 + d * (-503693759543819795341461 +
    d * (-6821155170578520835362765 + d * (48018046522848149106848412 + d *
    (-76482095954718195967174308 + d * (-654410762142763832716785938 + d *
    (4954681118935827968927191586 + d * (-14555001526904953132299210607))))))))))) + d ^ 12 *
    (-3664467416949488611305590960 + d * (236790652939600928245267843186 + d *
    (-1185986704876367852156451843765 + d * (3099880096934212138049820151902 + d *
    (-1666009287032259053255827906058 + d * (-26521502909409186101112538594472 + d *
    (151697106398576600627113820988553 + d * (-492709727648479147133410638542079 + d *
    (998668897643833531702300195163447 + d * (-448621084217817887940000436588361 + d *
    (-6427211277508407348097893695572585 + d * (34755564263776083593989132979798018))))))))))) +
    d ^ 12 * (-115977429389850705400957329874774412 + d * (289242159394700049251222573141069600
    + d * (-524893902913104746583706619858351853 + d * (444332071584517205800338718346351693 + d
    * (1456177005717884028397264135433675547 + d * (-9624456762140225541814803775402757325 + d *
    (35211226467599480815163697240838059226 + d * (-103056228008838459819848916872889767179 + d
    * (263482148697683778030212487411283387249 + d * (-610448031606698555908139529131468055241 +
    d * (1306988577564667647278544721921593147208 + d *
    (-2617408614192103939283758524528815407164))))))))))) + d ^ 12 *
    (4943346728338954971682160028976494646246 + d * (-8857798582200693915517917538244431833084 +
    d * (15128088620477826848914709293204581441405 + d *
    (-24716495007060310113098824269874253671520 + d * (38746783359599227645566936817002760576969
    + d * (-58427147289456301021676029595220264244563 + d *
    (84925393153412104806090347628585568894309 + d *
    (-119200381242470120987438421458327829017073 + d *
    (161803741395100122886142310891079840952640 + d *
    (-212676050044907779510646681250731519240013 + d *
    (270969876931996777733666168170587847370927 + d *
    (-334936162979061097256573612633550544506031))))))))))) + d ^ 12 *
    (401908370903151710257902504989850193385962 + d *
    (-468409644062319456466036990624482836949419 + d *
    (530391956874164294613534214833709117747859 + d *
    (-583594664620335576230114264756033654729130 + d *
    (623986323052531409379630684506885127448139 + d *
    (-648232799364824435281225594878120234642499 + d *
    (654121651841398876435268676266129132253488 + d *
    (-640871862417402940442926324507364723197622 + d *
    (609271443306304900933344748273510060566360 + d *
    (-561612093208980891592240751770893128868891 + d *
    (501425213768833643383102437524351896176616 + d *
    (-433059670972384943367161032106063058517101))))))))))) + d ^ 12 *
    (361170273217773546490375176187500775590983 + d *
    (-290200190869405641490698421575600181120464 + d *
    (223937303259985634868423672078737290397739 + d *
    (-165205191066167531101765351072744681799949 + d *
    (115719682856556422155688398562157927466623 + d *
    (-76109190925414565318966125048614399471638 + d * (46069068372367560257224230483866391960301
    + d * (-24602290920793346491250609571306963517649 + d *
    (10293107921025309630340361980106915321702 + d * (-1565889923115210878352703152761175385505
    + d * (-3105179272604065192330268326358841095083 + d *
    (5053145293547790096544815049669836081283))))))))))) + d ^ 12 *
    (-5343771104221128616829831945712931547752 + d * (4759267651539318375722930179457054363686 +
    d * (-3823499088876011296606677016612024145461 + d *
    (2850485680273235342931128443728787276519 + d * (-2000474283907334289509794196162709538536 +
    d * (1332375791798196966496309894186799206543 + d *
    (-846319532559232872596583785711241414822 + d * (514270365763107022835938266069202852414 + d
    * (-299524853172761391212866542226448178041 + d * (167399532557955700413595337563358669717 +
    d * (-89826665974494835531866252914212275531 + d *
    (46285415241408862599935673685199293490))))))))))) + d ^ 12 *
    (-22896528110648520382461589883672977454 + d * (10867722643580508068131580168133330991 + d *
    (-4945080519521455755174052501703358238 + d * (2154576597832396023920189938593420441 + d *
    (-897533336859346503478874899629341006 + d * (356804852147126078006509174199017945 + d *
    (-135057433958356007824176773968975840 + d * (48542899285108355310105461797339437 + d *
    (-16512817794753733836006728639809624 + d * (5295160050730746656391385198318156 + d *
    (-1592983863973368376658585365979519 + d * (446969747578761969345083289178718))))))))))) + d
    ^ 12 * (-116135337239300113593485329793905 + d * (27694967365669860982789678051968 + d *
    (-5993547801302562257077214249758 + d * (1159860448534646187421848965297 + d *
    (-196700373689000897051156727196 + d * (28386501739595236299961671386 + d *
    (-3326546825963630765112089154 + d * (291124955730718123212921830 + d *
    (-16108312046879725942483339 + d * (549489808331232548572858 + d *
    (-119684599055082082685010 + d * (24943013194441334170893))))))))))) + d ^ 12 *
    (1532393715181797980302 + d * (-1764516095975015250248 + d * (415587970778819604036 + d *
    (-52107110744046429835 + d * (2975885441973628623 + d * (120104766335046861 + d *
    (-31128810807616427 + d * (1317218571376040 + d * (16032234557543 + d * (10141576684455 + d
    * (-659994343293 + d * (-176394902061))))))))))) + d ^ 12 * (4984051501 + d * (1233660212 +
    d * (58451554 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_3 (d : ℚ) :
    orderSevenSelectionPolynomial d 3 = selectionExpandedAt3 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 3 =
      selectionNumeratorAt3 d := by
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
      selectionNumeratorAt3
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 3 =
      selectionDenominatorAt3 d := by
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
      selectionDenominatorAt3
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt3 selectionDenominatorAt3 selectionExpandedAt3
  ring

private theorem selection_cofactor_eval_at_3 (d : ℚ) :
    (selectionCofactor d).eval 3 = selectionCofactorAt3 d := by
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
    selectionCofactorAt3
  simp
  ring

private theorem selection_factor_at_3 (d : ℚ) :
    selectionExpandedAt3 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 3 *
        selectionCofactorAt3 d := by
  unfold selectionExpandedAt3 orderSevenDualKernelPolynomial selectionCofactorAt3
  ring

theorem selectionEvalAt3 (d : ℚ) :
    Internal.SelectionEvalCertificate d 3 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_3, selection_cofactor_eval_at_3,
    selection_factor_at_3]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 3 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt3 d
#print axioms solution
