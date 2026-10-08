-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:29:20.653993+00:00
-- url     : https://prove2.me/submissions/e9df1188-dae3-4282-8f8c-0827ad82c629

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval0.At4. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 4

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt4 (d : ℚ) : ℚ :=
  -36859543552 + d * (-87319904256 + d * (472509812736 + d * (-658472299584 + d *
    (-1864958894208 + d * (12328532651520 + d * (-32337117683136 + d * (39252274183296 + d *
    (46866956758272 + d * (-396933801710528 + d * (1276013250328896 + d *
    (-2983175360852544))))))))))) + d ^ 12 * (5731050462939840 + d * (-9505101380559168 + d *
    (13963462640151552 + d * (-18447322109278272 + d * (22128994921430400 + d *
    (-24248009572183872 + d * (24352407046840192 + d * (-22453132269505920 + d *
    (19009621280976192 + d * (-14755170034249152 + d * (10463602591215360 + d *
    (-6746926639500288))))))))))) + d ^ 12 * (3932597150697792 + d * (-2056070154465216 + d *
    (955133403487872 + d * (-392499948347072 + d * (145598619849984 + d * (-52138927544640 + d *
    (19386457798080 + d * (-7193916465408 + d * (2329062731904 + d * (-611428475136 + d *
    (152647575168 + d * (-49983465984))))))))))) + d ^ 12 * (17015736576 + d * (-3854074560 + d
    * (481356864 + d * (-93870016 + d * (46979136 + d * (-10627008 + d * (326592 + d * (122496 +
    d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt4 (d : ℚ) : ℚ :=
  -43637538816 + d * (-120423251968 + d * (774516441088 + d * (-1752167976960 + d *
    (643649656832 + d * (10427926418432 + d * (-42060345176064 + d * (91716589051904 + d *
    (-117837167061504 + d * (4470473681152 + d * (456950146034560 + d *
    (-1532367866040000))))))))))) + d ^ 12 * (3450746469402496 + d * (-6266319249219200 + d *
    (9734912798015232 + d * (-13307374889897152 + d * (16291951894393280 + d *
    (-18118855439248192 + d * (18564031254008128 + d * (-17792647187339840 + d *
    (16196039049640448 + d * (-14159798731217088 + d * (11935821880708736 + d *
    (-9662968941719168))))))))))) + d ^ 12 * (7450781327031232 + d * (-5424458171794368 + d *
    (3703194212444288 + d * (-2356954792076928 + d * (1389878745814720 + d * (-754093543202880 +
    d * (373865830007232 + d * (-168183800282176 + d * (67937748305472 + d * (-24191431836032 +
    d * (7367653236608 + d * (-1835265394688))))))))))) + d ^ 12 * (348910030336 + d *
    (-43984652800 + d * (2012328960 + d * (366352384 + d * (-54494208 + d * (-1356800 + d *
    (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt4 (d : ℚ) : ℚ :=
  9823837402043576963374306557952 + d * (-228980138967300581308679432699904 + d *
    (-5201673370432358418939413870411776 + d * (11160703702834668641320811622301696 + d *
    (147860254886712399041270325851455488 + d * (-863302742089207200205282339784228864 + d *
    (566706705066020224306645242679918592 + d * (13472732737410641273792834993309876224 + d *
    (-71183787915543064643043765673458139136 + d * (130635325346956117519651611906970746880 + d
    * (346723066036192913718509179642638499840 + d *
    (-3200749549004271878166124876098986049536))))))))))) + d ^ 12 *
    (10799889759213422409280279265215336939520 + d * (-15808494488359044447068367249252801052672
    + d * (-33631525027352055803574203406499284779008 + d *
    (294133345157348170928884218216788610252800 + d *
    (-1013387342591415656484035646261316399398912 + d *
    (2064205526050418464076328753937940429668352 + d *
    (-1216638151325484505518370349465160894119936 + d *
    (-9678015102034089924091427714134844602318848 + d *
    (49226364458182124206270359280066854150733824 + d *
    (-142576525780780965408642028274624873612181504 + d *
    (282882475920869937364580009740969962739597312 + d *
    (-308196267555090635111206945302260335311847424))))))))))) + d ^ 12 *
    (-365486766155564004502934588217200439676633088 + d *
    (3150536337708037486871934368309348319693111296 + d *
    (-10582579085032272621261346761358608362698440704 + d *
    (25678395249721894420115021372291529923421011968 + d *
    (-48516940129941002241098514116755576068354605056 + d *
    (66821406446432381764904082642762155458249883648 + d *
    (-36023352374111442953266336286946709335071784960 + d *
    (-155931157901948728640373040794184299335833878528 + d *
    (741441586251590181484301833364560686388980744192 + d *
    (-2139765105933489725235664027665000363687826948096 + d *
    (5021913863158356846891800854184512558397539745792 + d *
    (-10343739087555467627784459304224293178381534494720))))))))))) + d ^ 12 *
    (19302288322601299944035969460231222247663019491328 + d *
    (-33162596706467379689099775137511177156857621118976 + d *
    (52908712266854069407406304619926588628030134419456 + d *
    (-78700057434496533002955885043948565971184400203776 + d *
    (109163154917462582525885387046953615356102092783616 + d *
    (-140612512761623479099468690357764520539619721740288 + d *
    (166358310877582040563662784225337086780943431630848 + d *
    (-176302657211970087778694492794444207231764851589120 + d *
    (157031347803722843053282460981698089911838111956992 + d *
    (-92562101710264552777124999167477842162027211522048 + d *
    (-34186910563439057230851004842402842359105980727296 + d *
    (239279057430631349514015930594628470223628310413312))))))))))) + d ^ 12 *
    (-535209561443360615737787027144228285748887114743808 + d *
    (928270363401593893074804020641579777867201639088128 + d *
    (-1416255872166231783321672561478659356929734432260096 + d *
    (1986945791234208634798084482530013227963842445443072 + d *
    (-2617731326261834081394725559784332556938002111397888 + d *
    (3276606596759296056213162955253598595228535111024640 + d *
    (-3924547350772762076949616946515505885766513094033408 + d *
    (4519074963227239908978815602313224149761184342736896 + d *
    (-5018593004641362243187353432980570405675565516062720 + d *
    (5386925315126544758021018046065591451054024598224896 + d *
    (-5597411837797624851225980280336214687627952166535168 + d *
    (5635952350631660990168091641522034107110354908872704))))))))))) + d ^ 12 *
    (-5502531200208137059890089923724894520485918306992128 + d *
    (5210988872924934994073657086611248936667054014988288 + d *
    (-4787088549619663608795310114502605922693734037716992 + d *
    (4265203259746197367759602293547551336324300849020928 + d *
    (-3684165163627103391911961089965755498087097746325504 + d *
    (3082928242142775142053030762873253101881146891042816 + d *
    (-2496679087549041951065531025028169237717952284327936 + d *
    (1953897491147831991703024615564563814681158598787072 + d *
    (-1474655821369723691965696808579598511735789228654592 + d *
    (1070206070691129797224010201312618470828523203067904 + d *
    (-743688799550819133509366043660823603809132062441472 + d *
    (491648897261908023049736463518031026384113571987456))))))))))) + d ^ 12 *
    (-305977916536356875541236912697487183200960189562880 + d *
    (175918470474697419906958503019819505331982180024320 + d *
    (-89842582473421215606375553131137986079624359575552 + d *
    (36624151758566853028363062608652458283496215150592 + d *
    (-6537124063449022126444550880833911844064933183488 + d *
    (-8296561866994642700076242942137385822872148377600 + d *
    (13823873544683366261906632354104403513000438267904 + d *
    (-14229250497829296612102429724260232794633173467136 + d *
    (12242131774837354906155778244599492245646476836864 + d *
    (-9490129475231357308945909451998386357516376473600 + d *
    (6832710395040367409430688798026175189600705970176 + d *
    (-4638802728828760588387227154024313237274783383552))))))))))) + d ^ 12 *
    (2995232537373834023877427549454416679000026120192 + d *
    (-1848957195499253469573179175860157621015543545856 + d *
    (1094774536345932566216922731443417399997265346560 + d *
    (-623074023742044732039058724226372113832642084864 + d *
    (341306773056906091978152936157151870584568938496 + d *
    (-180081985057427417114258340029942161439205359616 + d *
    (91550669364112300504410315762647326991258222592 + d *
    (-44845272337188762298336379575311780825352110080 + d *
    (21159612739956516228444079714446079980584566784 + d *
    (-9611540232268726980790133434520482630022201344 + d *
    (4199741350241560830636648609740009322743595008 + d *
    (-1763349122138175763842658267965327320285708288))))))))))) + d ^ 12 *
    (710508972191554354871654208241702031615590400 + d *
    (-274298890780254940703812623625965065321316352 + d *
    (101268481025066672040749832136335551064702976 + d *
    (-35672929622095733881673479998747849979330560 + d *
    (11957954080352538501619050607777166788919296 + d *
    (-3802385716352872470930679718360580099145728 + d *
    (1142639289438176163036466267822305912029184 + d *
    (-323053420389854524817678563100269178781696 + d *
    (85469636676262297091133575092860678307840 + d * (-21021110735832355054203294738243510599680
    + d * (4766602257346298594583913585731059056640 + d *
    (-985816600725741054465609964572860481536))))))))))) + d ^ 12 *
    (183243339476647411465055690148467965952 + d * (-29958846795992573029671573747578175488 + d
    * (4158617051569624922846425888739295232 + d * (-457437830534751765265928990829051904 + d *
    (32889521380990670531058423206772736 + d * (-4115722584443482724888895553536 + d *
    (-377731751651582632871949149405184 + d * (49971897713714807671892933083136 + d *
    (-2736835720728737077660471787520 + d * (392727581756158456953286164480 + d *
    (-225180869769247852653825753088 + d * (62670973840566671806293868544))))))))))) + d ^ 12 *
    (-9548248294123844283567177728 + d * (667257746474399531769790464 + d *
    (40485855222581459083067392 + d * (-14699630053980339003981824 + d *
    (1358090441757887284117504 + d * (-11757391697799042039808 + d * (-6821186615171018915840 +
    d * (223072780274561187840 + d * (12076246852354965504 + d * (4547649004854050816 + d *
    (-327689571549052928 + d * (-56301080615059456))))))))))) + d ^ 12 * (1584109792002048 + d *
    (344889942081536 + d * (16128634257408 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt4 (d : ℚ) : ℚ :=
  53459294829558112452608 + d * (-1204347611596613054627840 + d * (-29325132234742703811723264 +
    d * (39666217981127883663343616 + d * (878117205154580754813943808 + d *
    (-4093071823454311492696932352 + d * (-1411493036971147993533120512 + d *
    (79013418359747519531751153664 + d * (-325605199263292615689708094912 + d *
    (331002001826871337514680547301 + d * (2697424280873382912414177319218 + d *
    (-15941199440420495198387228600179))))))))))) + d ^ 12 * (41875098018247217109877988953359 +
    d * (-25963490133731886514811570854598 + d * (-275596432807775287120578884803877 + d *
    (1424921319071821154864804579816066 + d * (-3889907068472519797384325961425538 + d *
    (5634124180491582473836528475340248 + d * (4487646978752422280383505138469832 + d *
    (-57576302127509683894360500009601692 + d * (208786698162989313315068323967548320 + d *
    (-495824242856294433805806957466271471 + d * (766888764673304875654322907546488300 + d *
    (-254093909358309051200864394188120744))))))))))) + d ^ 12 *
    (-3180098783053058439276235625420655119 + d * (13883078827325596277286631366388403738 + d *
    (-38270668564533828879390606021657260099 + d * (81036203256298243496914883522394092258 + d *
    (-132595703980489286624792231426954343349 + d * (139731362131565117094907246797718525871 + d
    * (50956617211705773846977851569613862815 + d * (-787218355470405243043744644214541048200 +
    d * (2749044375326052288764190320157781120831 + d *
    (-7126162315400466791527527948661808044147 + d * (15815012862975757441716032533286965232252
    + d * (-31595860402529329336117399385554934819407))))))))))) + d ^ 12 *
    (58233461584753639948422110324238473880072 + d *
    (-100436210307498116707023246175147910984179 + d *
    (163615114883268634610486506445167404215208 + d *
    (-253408576803383719508042124426978262449175 + d *
    (374980146654235622987534334392342856828110 + d *
    (-532147443844746729888309439352428939057633 + d *
    (726450584560998301576085023122151882707407 + d *
    (-956305850031036629185040294349832575658927 + d *
    (1216404761891139706722653180271614883921001 + d *
    (-1497504226784860093401781020519249842907813 + d *
    (1786709553435906318151059586497915142806301 + d *
    (-2068284256098931118202090410783068572995273))))))))))) + d ^ 12 *
    (2324938826270878067425139925414958257977567 + d *
    (-2539468475823375319303991349240927242725661 + d *
    (2696541667899846231151798410657074701013134 + d *
    (-2784400155056117782772301533601216416123043 + d *
    (2796226704263793731295892121702245831990879 + d *
    (-2730972620187076717816786940994989002755040 + d *
    (2593510618679705713809507183207288496857519 + d *
    (-2394079252650862965318935164239310161203644 + d *
    (2147096135373488554038245062625203547261865 + d *
    (-1869517835444406029363784538137324410280326 + d *
    (1578994019545829149646997293384115008112219 + d *
    (-1292087217251069006653699024125294093840791))))))))))) + d ^ 12 *
    (1022802580505334651291071398757806991793316 + d *
    (-781601345426950649822980369669574810848067 + d *
    (574974795245499240208835758438010845551860 + d *
    (-405555033791533641494768554771558184537619 + d *
    (272656222193415371512925098440003144091270 + d *
    (-173089696831839076367294397863391204346429 + d *
    (102083479473404915343907580336912267690721 + d *
    (-54156703651357191141467053631397526978831 + d * (23841574255829928084061532425540400364985
    + d * (-6196362154253508258407139425797602895434 + d *
    (-2899426158282658796887345594113137464631 + d *
    (6640488603992908247152055256889802003692))))))))))) + d ^ 12 *
    (-7333720527419421922118396166137836777514 + d * (6524564892295000628532103940415860570411 +
    d * (-5162673250608118100121566115520737742423 + d *
    (3769593499970628501617801203186295169950 + d * (-2585074086985148163111285612199053800510 +
    d * (1681176593589479984051976997780848097361 + d *
    (-1042825558036241597906708467208855939188 + d * (619174932334085228984925877135064651270 +
    d * (-352681327529542842909012516066042381384 + d * (192973753222589061336621302895093564115
    + d * (-101500034141025663719581081351984130015 + d *
    (51331373778209883555582238952657692797))))))))))) + d ^ 12 *
    (-24955950118034990424522909192583835892 + d * (11657786375139743356646493073592273782 + d *
    (-5228118049430049697354678613511825858 + d * (2248330054882891180829423203673245976 + d *
    (-925792661491647357692480675135453090 + d * (364336392264850772332470003561939817 + d *
    (-136723994544159172583666827492937548 + d * (48792269380794710337615684481557276 + d *
    (-16503801816140483269627058948991289 + d * (5269918411872497207409877740819936 + d *
    (-1580874586157567856003347034647117 + d * (442878714806982587838712741671983))))))))))) + d
    ^ 12 * (-115025612124664086871896178883846 + d * (27446323142009041242980136711099 + d *
    (-5947879726757395530467055949302 + d * (1153240047034014960272837997206 + d *
    (-196009858736119552735013344642 + d * (28346829828576106931703890011 + d *
    (-3326172857086915853613668290 + d * (290516457991692335589621988 + d *
    (-15775347500188960420886009 + d * (471972500521665130994487 + d *
    (-109626838681973229481659 + d * (24418131778358851413585))))))))))) + d ^ 12 *
    (1472532546168350915899 + d * (-1750843892607123542694 + d * (414737800678238740622 + d *
    (-52132002152797487553 + d * (2978411654770329982 + d * (120610822111894178 + d *
    (-31127115163467604 + d * (1308074571582176 + d * (15929613466760 + d * (10201751618141 + d
    * (-655974050857 + d * (-176243714059))))))))))) + d ^ 12 * (4988498479 + d * (1233711012 +
    d * (58451581 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_4 (d : ℚ) :
    orderSevenSelectionPolynomial d 4 = selectionExpandedAt4 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 4 =
      selectionNumeratorAt4 d := by
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
      selectionNumeratorAt4
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 4 =
      selectionDenominatorAt4 d := by
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
      selectionDenominatorAt4
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt4 selectionDenominatorAt4 selectionExpandedAt4
  ring

private theorem selection_cofactor_eval_at_4 (d : ℚ) :
    (selectionCofactor d).eval 4 = selectionCofactorAt4 d := by
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
    selectionCofactorAt4
  simp
  ring

private theorem selection_factor_at_4 (d : ℚ) :
    selectionExpandedAt4 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 4 *
        selectionCofactorAt4 d := by
  unfold selectionExpandedAt4 orderSevenDualKernelPolynomial selectionCofactorAt4
  ring

theorem selectionEvalAt4 (d : ℚ) :
    Internal.SelectionEvalCertificate d 4 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_4, selection_cofactor_eval_at_4,
    selection_factor_at_4]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 4 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt4 d
#print axioms solution
