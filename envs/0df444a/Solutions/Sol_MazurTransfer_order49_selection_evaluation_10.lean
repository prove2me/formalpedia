-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_10
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:13:50.301989+00:00
-- url     : https://prove2.me/submissions/e78ee086-8cd9-44b7-bb24-98741af43842

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval2.At10. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 10

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt10 (d : ℚ) : ℚ :=
  -1906624000000000 + d * (-944885952000000 + d * (3538210200768000 + d * (-7586316368291904 + d
    * (8563860938899584 + d * (1582246817662464 + d * (-23428985920453440 + d *
    (47338221811780224 + d * (-60362808772853376 + d * (48596720870312512 + d *
    (-3478043631526848 + d * (-69093326330309952))))))))))) + d ^ 12 * (153365176164477504 + d *
    (-231720678868194624 + d * (288218302139182464 + d * (-312688568359346496 + d *
    (304383392092046976 + d * (-270079408392204096 + d * (220075565049990016 + d *
    (-165427719421847424 + d * (115194089955400128 + d * (-74406806574917568 + d *
    (44418650662137600 + d * (-24392839604295168))))))))))) + d ^ 12 * (12313279779453120 + d *
    (-5711066434100160 + d * (2409296937628416 + d * (-907748242801856 + d * (306544528877184 +
    d * (-99736147392576 + d * (34701506375232 + d * (-12327740418816 + d * (3730509522048 + d *
    (-870537582336 + d * (193697597568 + d * (-64038679296))))))))))) + d ^ 12 * (21781640064 +
    d * (-4505793216 + d * (442552896 + d * (-80972224 + d * (47836224 + d * (-10613184 + d *
    (326592 + d * (122496 + d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt10 (d : ℚ) : ℚ :=
  -2259264000000000 + d * (-1242448518400000 + d * (5347546709248000 + d * (-12813466526039040 +
    d * (19058139469451264 + d * (-12766669073502208 + d * (-10838699028867072 + d *
    (43311662617857536 + d * (-75040983055732224 + d * (93565373334604672 + d *
    (-83764530266638976 + d * (43232623015269312))))))))))) + d ^ 12 * (18763741956183040 + d *
    (-88375996027646336 + d * (148065850632862464 + d * (-182808862766913088 + d *
    (188638890900728768 + d * (-171614308902459328 + d * (141855291717946048 + d *
    (-109213991003009984 + d * (80219197922916608 + d * (-57087919035715392 + d *
    (39454531562489984 + d * (-26376366451215488))))))))))) + d ^ 12 * (16987861186932160 + d *
    (-10492205158408512 + d * (6178807047014528 + d * (-3450156969464448 + d * (1815572603437120
    + d * (-893084992589376 + d * (407354394709824 + d * (-171453882192064 + d * (66276833372736
    + d * (-23180594951552 + d * (7091111658368 + d * (-1796872033280))))))))))) + d ^ 12 *
    (348192653824 + d * (-44406432256 + d * (2002947072 + d * (374695936 + d * (-53652480 + d *
    (-1350656 + d * (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt10 (d : ℚ) : ℚ :=
  1419260805691211776000000000000000000000000000 + d *
    (-61626720773371395440640000000000000000000000000 + d *
    (-85893544850849029566606868480000000000000000000 + d *
    (593003636772561578659837087842304000000000000000 + d *
    (-932297250807390511511026913747927040000000000000 + d *
    (-731149345119792642483680459786013900800000000000 + d *
    (7598391217003302823716847248461248908492800000000 + d *
    (-18572012256429197136634185274041069361902387200000 + d *
    (18531904430957322801285898269450348177369333760000 + d *
    (24441787266448393510460061036761518673423499526144 + d *
    (-139542996278969032242052455463563668334191287992320 + d *
    (297192705857400424779971999356957883016639279529984))))))))))) + d ^ 12 *
    (-333931365607220810642883456234335837460646929104896 + d *
    (-64626052731496726075338405291087720139135128961024 + d *
    (1219060857638148884819491531018950248342902962913280 + d *
    (-3093875244304297400608165727258296492258967743627264 + d *
    (4812102634311285201598168688110095057002709485617152 + d *
    (-4373751474987985562677695707108643312461243166490624 + d *
    (-944376093742025828627617790873492124587339224186880 + d *
    (13163467985275932586496984393398691668565106077466624 + d *
    (-31303773205970297702399709320920003729799973717934080 + d *
    (49118632156561376353493955762837971153792692975828992 + d *
    (-54420011854909422551713021110830146133808041105555456 + d *
    (31566816699014745006945223113227836296551248906682368))))))))))) + d ^ 12 *
    (32282637255873335146862628424659782441572730772127744 + d *
    (-138370362400111432852027132181590647198245297285496832 + d *
    (268205083664712846762881450334598221889564314924482560 + d *
    (-380440136523604773974670814601854355656721148979183616 + d *
    (416433774808121950814462983001594789693766554844397568 + d *
    (-315473486277081892202440634263297614736039507054034944 + d *
    (36717369907528780045128507608502535155002868995457024 + d *
    (418717884107835075308264820128928292591193770751950848 + d *
    (-993705403120731044483232318684173207955253657666584576 + d *
    (1575832785869964559861228259326061987820002589615325184 + d *
    (-2015358594714551458693292275912088141440706387191005184 + d *
    (2157187442091793576959064029088701632593368179778519040))))))))))) + d ^ 12 *
    (-1878701851542641922040020324819045262245574854730055680 + d *
    (1122938890060369345227724561770499618690091674800226304 + d *
    (82288108528508543973752729130864520915450414738964480 + d *
    (-1624621481379327563110225769952136033686087086955298816 + d *
    (3326485174633166703845400303972623094604033226091003904 + d *
    (-4978134991151606650176183016448872269512289774731788288 + d *
    (6375944650537458866241566633868353206558104001959690240 + d *
    (-7356994212931838418392091246121941243995058294270984192 + d *
    (7822984637179389871477391722228180702405258641504206848 + d *
    (-7749911117804458764589835911021067202949347410347294720 + d *
    (7183609578514295922893873120738088760138754085780455424 + d *
    (-6224250346641456432615514316935554794511288665991282688))))))))))) + d ^ 12 *
    (5004523426865051504479986576667454870849301671309737984 + d *
    (-3666546060323091813976907653846305327539650618164248576 + d *
    (2341695083287505424923498438455667835053372638215798784 + d *
    (-1136083948600645918707580482987833283403287069764354048 + d *
    (122751021442786946272844356926666125147084795141160960 + d *
    (659809415679310600512285682030877615138144290621882368 + d *
    (-1204126376576967403514870120433075343440566816200720384 + d *
    (1527058430224352899893163810626094081295771829073084416 + d *
    (-1661748569276071505849098611179818225635080158964350976 + d *
    (1649734133390595967333173062355006070750498628077617152 + d *
    (-1534244764303964000954569423822817403644034467393437696 + d *
    (1355229205289834138602697889017385810700431810048557056))))))))))) + d ^ 12 *
    (-1146234768841400867283382803941934461573600673068482560 + d *
    (932965992175785491827344070284015888251922895046443008 + d *
    (-733176789048857744207623445571736037503503370423369728 + d *
    (557484993228104106038957208219802089707514930272141312 + d *
    (-410711359839790052159984497429777557891608408349736960 + d *
    (293407828768668244524106495881916947005108838921404416 + d *
    (-203326905481064132310429189602932698735568283566604288 + d *
    (136675561981102277515719116180385464674257776029466624 + d *
    (-89079098380553985481559090596202155888565351225753600 + d *
    (56244594539497859117652101944625986641145481858383872 + d *
    (-34356705999046484958977187319203987386420353589575680 + d *
    (20261538407552694063781959458221017391231871912247296))))))))))) + d ^ 12 *
    (-11500875527319585371937487895389005162278968424923136 + d *
    (6254168116291690119784315966696931172777949072982016 + d *
    (-3234486173661111918795136077359676110514995593740288 + d *
    (1571314975372344657024826538518705503714657185824768 + d *
    (-700571327562249019593868516642662878262368669794304 + d *
    (272148945328548976780130656710434188818538723278848 + d *
    (-78205416677144422241235208573322118895263634948096 + d *
    (1079775418712213103480020861827536408590132445184 + d *
    (22401750360555592908715376346464416571325328916480 + d *
    (-24102561061838506822206847242924690691472534274048 + d *
    (18853207124475656292597007611000314123451579498496 + d *
    (-12787864790318060283288827487655093440402107138048))))))))))) + d ^ 12 *
    (7941191609142216904776880392895331188053051179008 + d *
    (-4623891086580444060270854715920592703049895247872 + d *
    (2556131133138969678386538053012430563296109395968 + d *
    (-1351283283027189142454158787677602370302203658240 + d *
    (686144888415026735413400316397006046892105924608 + d *
    (-335577330813055432366850327105594356294815055872 + d *
    (158349886868236367618340856424584163431334019072 + d *
    (-72162967556035178887513666282719688809272311808 + d *
    (31773883768904538197853342456393407427908206592 + d *
    (-13517200857448262746176161140434549431668572160 + d *
    (5554009944915798350471596842506747203634069504 + d *
    (-2202567395193371559668949660163009979301232640))))))))))) + d ^ 12 *
    (842200297232922228266215498952197671354368000 + d *
    (-310088545672198267103111273765290981597118464 + d *
    (109751577707446342023702084360307989936603136 + d *
    (-37264321389375173201547509908779474092556288 + d *
    (12107095455064224361858256723778216983265280 + d *
    (-3752519596597825379840139367227853819084800 + d *
    (1105420380306689444907914725407368050900992 + d *
    (-308095186728057648841428838058066142560256 + d *
    (80794743987133555601692948918350363492352 + d * (-19798701975100436771248047391918666547200
    + d * (4494526502770734144937366407166987599872 + d *
    (-934632125921191086661168569329830068224))))))))))) + d ^ 12 *
    (175332996114806418983924154941412737024 + d * (-29017102590538492170513377802752098304 + d
    * (4085126564148310397015870987543511040 + d * (-455525759744974331543455407366995968 + d *
    (32813689892172966487551995982905344 + d * (186614973208001079824916535050240 + d *
    (-441917519578186134972997812092928 + d * (60665914971675065496119991074816 + d *
    (-3492323088770834217422807629824 + d * (313145601332755777711902818304 + d *
    (-197477522126507635616147046400 + d * (59595065813327087242572726272))))))))))) + d ^ 12 *
    (-9481839485106310052412391424 + d * (688699269465201670477578240 + d *
    (38599905783061412588290048 + d * (-14747978628304860707028992 + d *
    (1361904059442315155734528 + d * (-10141602524639663226880 + d * (-6844101988214254075904 +
    d * (202293535671004692480 + d * (11950390789666504704 + d * (4663045406794711040 + d *
    (-320383139407462400 + d * (-56024567575478272))))))))))) + d ^ 12 * (1592021417459712 + d *
    (344975883370496 + d * (16128665714688 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt10 (d : ℚ) : ℚ :=
  639127649000000000000000000000000000 + d * (-27555466379172500000000000000000000000 + d *
    (-47532933187503418020000000000000000000 + d * (269008404242077766816021000000000000000 + d
    * (-319012995621863815924501210000000000000 + d * (-607782870716086730883465970450000000000
    + d * (3531381696273822768468193834397200000000 + d *
    (-6995511933155944086161616810072972800000 + d * (3699083237548983679142933039001468365000 +
    d * (17810861054542434592231985425800930055431 + d *
    (-61678536565898296076111506951436073205650 + d *
    (103068766381050987229115136560935323940691))))))))))) + d ^ 12 *
    (-70128910189530396003493716296294377557063 + d *
    (-138399115464190230166141893453049643001116 + d *
    (574590201776379865714927012567618378096903 + d *
    (-1113631288255789136441011506738030208798834 + d *
    (1345003600855524500871961969582506415212822 + d *
    (-603009181338143328867599192948400147481882 + d *
    (-1753476062571343100316044917973546539037618 + d *
    (5815597473950897540245234776967508256848928 + d *
    (-10537478008060223163811306586857663067796882 + d *
    (13436237276092515873421150764723517707397801 + d *
    (-10964053121361020715604907365620782778941842 + d *
    (-255253891876125106660757147400833587124216))))))))))) + d ^ 12 *
    (21532764677890680872310140286606237650041945 + d *
    (-50215944593362664400761041285462122474529164 + d *
    (78702579047648215291936985614402743995079685 + d *
    (-95178301249694593747500653603598658216927492 + d *
    (86357505080681718561615494447929273043251541 + d *
    (-41721061704294743528264492749057946442582001 + d *
    (-41972434353611853941056637948728294499711279 + d *
    (157451023975769964184074005482644947729029820 + d *
    (-286274261431869802697362142954827239598886609 + d *
    (401304240571921947257566317708975038522403215 + d *
    (-471855457539877836369281883976052801684985514 + d *
    (470222858967466884030761205793907895404915909))))))))))) + d ^ 12 *
    (-377872215209530257231888346227605114863764594 + d *
    (189716477154821610293020415748471557542536437 + d *
    (84496607097076832839630212537580506837114738 + d *
    (-421840626561799201922524433994656593865259385 + d *
    (790306143102829040490574741812228164134203026 + d *
    (-1154239502552213415152127932516895439030565341 + d *
    (1479887926480814221784225473689552538362282023 + d *
    (-1739990014968124181462568792631150262621193103 + d *
    (1916729857389796285536529896597709317455868799 + d *
    (-2002818510889389122266838315715895902182802081 + d *
    (2000863360328012288809079726408567721461119705 + d *
    (-1921461010202073596179113700594950893242736699))))))))))) + d ^ 12 *
    (1780576095641857615225426482991001558490427559 + d *
    (-1596758816923633809420396851461733514759491015 + d *
    (1388645585736070400823548348184022403410280380 + d *
    (-1173027762064183346795612793764424340150628871 + d *
    (963608278114489015342752084904546998271956217 + d *
    (-770428343344767703248665373893241637937465878 + d *
    (599853581896313800648604342209731081858913941 + d *
    (-454962972496938025635338948252777310396080350 + d *
    (336176743216075229606729391829471332194520513 + d *
    (-241978430071884840599627165652661686508176440 + d *
    (169619303330670205423412047616888302217252973 + d *
    (-115730565353082184400407222169874806533639655))))))))))) + d ^ 12 *
    (76803595463063040063585388360541874534944296 + d *
    (-49527274809521018720874942947008311670398083 + d *
    (30992334226588638711852914001835123346230040 + d *
    (-18785500247717694160391817103038035000288589 + d *
    (11001831433341243951151240943249706184205596 + d *
    (-6203610593927047412465856944515537765907305 + d *
    (3350374400643249029666768050570598788938291 + d *
    (-1718957722428845952476028574068015052724899 + d *
    (826320724367870155132002885607182553708225 + d *
    (-362458359671697846374398061430773952292014 + d *
    (136424719979379038539663939571665828519777 + d *
    (-35592649415891786572467250936213802303420))))))))))) + d ^ 12 *
    (-3413705196968156600867061228997514652296 + d * (14402781592316115573022745719146916844513
    + d * (-14289398589870207481684780770568478032027 + d *
    (10852723231190247817845264087490541264948 + d * (-7241737490023234527721278302533579402370
    + d * (4446202027253883278145317042083500019169 + d *
    (-2565169510363726168807091005252349957140 + d * (1406335891546654986941869419373265755904 +
    d * (-737460304190709285876565414498647921654 + d * (371353603588218699367672244177544344671
    + d * (-180007708083961712198996434270638211457 + d *
    (84113374848369015586522195865168470341))))))))))) + d ^ 12 *
    (-37915191664773737229159691071295084842 + d * (16489219911376867443435463576169112286 + d *
    (-6916594810507428846528504264878908620 + d * (2796274784769655684894561803653386466 + d *
    (-1088382480019216499797595107112120762 + d * (407230120686536159517693219777310939 + d *
    (-146186406600429483616930847293032166 + d * (50225153323494938734312513164270216 + d *
    (-16465269751161377705662828871461273 + d * (5131206007852058381689032616807938 + d *
    (-1512962168245413679989014082858665 + d * (419565644496017352912137195206007))))))))))) + d
    ^ 12 * (-108597930712880769620067990106868 + d * (25980901033304436699177582987213 + d *
    (-5673558282813204832975287532692 + d * (1112577264470440889054544992162 + d *
    (-191636369464477236813530246296 + d * (28079286234710693676722429623 + d *
    (-3322894122708437663217511858 + d * (287248033442833296300923752 + d *
    (-13858736490132998698554263 + d * (13132685851467557409729 + d * (-49116133347291001514331
    + d * (21210256948530008298171))))))))))) + d ^ 12 * (1113044241846536892403 + d *
    (-1668294790552963003686 + d * (409670018546459479814 + d * (-52289077511552733657 + d *
    (2993134591553320492 + d * (123694935194547938 + d * (-31111968557688406 + d *
    (1253429309648156 + d * (15320398877456 + d * (10562888291339 + d * (-631852107955 + d *
    (-175336586047))))))))))) + d ^ 12 * (5015180347 + d * (1234015812 + d * (58451743 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_10 (d : ℚ) :
    orderSevenSelectionPolynomial d 10 = selectionExpandedAt10 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 10 =
      selectionNumeratorAt10 d := by
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
      selectionNumeratorAt10
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 10 =
      selectionDenominatorAt10 d := by
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
      selectionDenominatorAt10
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt10 selectionDenominatorAt10 selectionExpandedAt10
  ring

private theorem selection_cofactor_eval_at_10 (d : ℚ) :
    (selectionCofactor d).eval 10 = selectionCofactorAt10 d := by
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
    selectionCofactorAt10
  simp
  ring

private theorem selection_factor_at_10 (d : ℚ) :
    selectionExpandedAt10 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 10 *
        selectionCofactorAt10 d := by
  unfold selectionExpandedAt10 orderSevenDualKernelPolynomial selectionCofactorAt10
  ring

theorem selectionEvalAt10 (d : ℚ) :
    Internal.SelectionEvalCertificate d 10 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_10, selection_cofactor_eval_at_10,
    selection_factor_at_10]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 10 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt10 d
#print axioms solution
