-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_16
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:06:10.865984+00:00
-- url     : https://prove2.me/submissions/0f9fe23a-5e09-4aa5-a7df-420b8f66819a

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval3.At16. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 16

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt16 (d : ℚ) : ℚ :=
  -517425773984874496 + d * (-124249318285639680 + d * (333405084764602368 + d *
    (-729512715481714752 + d * (1010883847640010624 + d * (-519990047571294720 + d *
    (-463869245469438144 + d * (1308146345816800896 + d * (-1776210524807394816 + d *
    (1736719595384197696 + d * (-1126376385451676352 + d * (255210660509611968))))))))))) + d ^
    12 * (555704399138667456 + d * (-1167181971202189632 + d * (1511080333872830208 + d *
    (-1567968003685764672 + d * (1410030305853793152 + d * (-1142239326662521152 + d *
    (844985074741406080 + d * (-574169343270815616 + d * (361901749619829312 + d *
    (-213000457043442624 + d * (116345748099688704 + d * (-58440742709792256))))))))))) + d ^ 12
    * (27105985319532096 + d * (-11748016794377664 + d * (4715914617852288 + d *
    (-1690081030331072 + d * (531584215985664 + d * (-159365608325952 + d * (53098809772224 + d
    * (-18619022552832 + d * (5404750211712 + d * (-1140951251712 + d * (227265988224 + d *
    (-77246909952))))))))))) + d ^ 12 * (26655536640 + d * (-5155106496 + d * (403748928 + d *
    (-68074432 + d * (48693312 + d * (-10599360 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt16 (d : ℚ) : ℚ :=
  -613197634810675200 + d * (-159795067916124160 + d * (502335036140290048 + d *
    (-1174134745590939648 + d * (1813565257119340544 + d * (-1510482603163675648 + d *
    (418113438709622784 + d * (671190233218715648 + d * (-1546410227214825984 + d *
    (2118161180644235776 + d * (-2066652563685525632 + d * (1522220577791641152))))))))))) + d ^
    12 * (-807931556910954368 + d * (102396974949463936 + d * (446961025874350848 + d *
    (-718559664103900096 + d * (741791340376680896 + d * (-630291406622933056 + d *
    (474024918621779008 + d * (-326461180868499776 + d * (213632923656943616 + d *
    (-136425625620958656 + d * (84738870971094656 + d * (-50626678578298496))))))))))) + d ^ 12
    * (29197782299555776 + d * (-16347185024884416 + d * (8816839113766016 + d *
    (-4530628456709760 + d * (2209460173428160 + d * (-1018321366919232 + d * (438751550460096 +
    d * (-175173814922560 + d * (64853417801280 + d * (-22193367763328 + d * (6810513897344 + d
    * (-1757899943936))))))))))) + d ^ 12 * (347568985600 + d * (-44826958336 + d * (1993565184
    + d * (383039488 + d * (-52810752 + d * (-1344512 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt16 (d : ℚ) : ℚ :=
  28520729986858431104885331620958181649211530030350336 + d *
    (-1298716807170933242463012275685810197769067391468175360 + d *
    (-67181745569685432436236716000600908037827824103456768 + d *
    (4648039689803202184976357178306753121868672885447458816 + d *
    (-9091192816064480344384800382271604760982445345648672768 + d *
    (9201989354437351957594007480686736508095939792362012672 + d *
    (8193104837418663002377201369240847544317872905232842752 + d *
    (-45988810415698600238600002765181416485198637708372606976 + d *
    (81477916828965910295710540100564381848440263882378838016 + d *
    (-75458060237878665004203503641884572293007662189142343680 + d *
    (-10815132331545275211925711758842370380408280121823461376 + d *
    (181750844183506748520947760388721097570365156144301211648))))))))))) + d ^ 12 *
    (-368404127716520606157822135256560002714791701831678951424 + d *
    (438043563328493356379559396825817068645991049656174641152 + d *
    (-256319827487716023309639033258325219663653852246494937088 + d *
    (-230663012763369207793445945755550350819749310388469760000 + d *
    (922281092131844586264490133301276737409892827258370129920 + d *
    (-1551100863852832827682561905869279228806194765347443179520 + d *
    (1769382661722444843362900145983712136664065624484321689600 + d *
    (-1300801512707055278840618422649222260204668156887540957184 + d *
    (90141612587935216738754869066903095322286832173555122176 + d *
    (1615986045422966148671801331380623531730995111451746369536 + d *
    (-3311200487302814402069423975016504290524784706494537400320 + d *
    (4393395360385530225222276472197373847993350710150344212480))))))))))) + d ^ 12 *
    (-4384627099728467932752550155118457125356240735189460582400 + d *
    (3118056805700309916945054429394564764491387020333059670016 + d *
    (-818418081600111028823218190065301062556013415467257692160 + d *
    (-1957846939285097730273966152166922285705433962088909766656 + d *
    (4498588725997677982411715306672658424827081471526034210816 + d *
    (-6157556902548960758451390960674552065859418809484710772736 + d *
    (6541446485588400872472494297893211154129729077130435231744 + d *
    (-5603732713229133493083160438116997621571986527801622659072 + d *
    (3625145496994527912909841325634475404436173379843580755968 + d *
    (-1102234753790147298117522605210384788356377545519475458048 + d *
    (-1407105854963242795635762196715622572694711445472454639616 + d *
    (3428134547268368308586366256407847406919744067846906314752))))))))))) + d ^ 12 *
    (-4665037409285379002074780764827100915623874130930588450816 + d *
    (5032207874511274442246365559741637789525676352233741746176 + d *
    (-4627778001869414278407192116936131358061183565528955355136 + d *
    (3670811990124902048666576557988917319474725239514045349888 + d *
    (-2427504261218351517167779227449221604157546249732161011712 + d *
    (1147175634003080145127883726344856038725326755180138987520 + d *
    (-20064931200877859979088978859929206364411277485005078528 + d *
    (-840279131720744118105990294892848434017978256863051382784 + d *
    (1394051351085029963312331079909664316137397780109557760000 + d *
    (-1659116604729242422776299467569055865525591268968430567424 + d *
    (1689560389309254225963894733870980076559288015099162001408 + d *
    (-1555001712191286870873994645211095017957415565386156343296))))))))))) + d ^ 12 *
    (1324399275657556610053855482040722977459121404339830128640 + d *
    (-1055761936447384508594071948372736987223742662057442672640 + d *
    (791455583696294199378524711453456930355685451169266139136 + d *
    (-557824972818475837044030421018571254589374340793459015680 + d *
    (367524424204399622050701719258473716988381707021523353600 + d *
    (-223080580782948689699448051217633924724203791798078799872 + d *
    (120582271889818680126128108640439349376660608555124260864 + d *
    (-52827928559375710358486540523632346058119018177998094336 + d *
    (11642050800876453769689205971538003936346278217804677120 + d *
    (10655863972707941784617027066531226309885055320006066176 + d *
    (-20491370209916370995247610019653301709668173607506542592 + d *
    (22786422399827734946422144614086220536748656198780452864))))))))))) + d ^ 12 *
    (-21028912158366168026198831276542447098663154823517437952 + d *
    (17504475190005353294701379709108775840727545767948976128 + d *
    (-13581562817283784221114328550868407659017869770415407104 + d *
    (9983867210134220692321554250554284849197586568100708352 + d *
    (-7017474214371930392767058023613730183986059602455953408 + d *
    (4742557360549789695300371058563015919741903686621986816 + d *
    (-3092568858380121361484496615657422798842053176734515200 + d *
    (1950159495551955760414890406611004275531279676761178112 + d *
    (-1190845334740607498072786638172576372972005014739091456 + d *
    (704666179568097801678050264817438633549817971708002304 + d *
    (-404137218569413793359019305085713685602274726251855872 + d *
    (224567608693989641889308954530042136541763296509296640))))))))))) + d ^ 12 *
    (-120798107807206714799826821564570381087065473546715136 + d *
    (62806961067983185803676270600620907815013191318503424 + d *
    (-31488368849269220408719197651068097378403041343438848 + d *
    (15166481430270829713505167365012830108494366709645312 + d *
    (-6977472173847132513693767710927920081097566308532224 + d *
    (3037050874529302098505390506538790584096436058324992 + d *
    (-1229560976103368038656703123945383898934328838586368 + d *
    (447158291613893618667057753919345223012721966186496 + d *
    (-133401618146100732648555356618897182069248513015808 + d *
    (21266070172459981935370774765257865243758542192640 + d *
    (10864549030239513727031292299042925534917743083520 + d *
    (-14956047121796556789171115107180311301328518250496))))))))))) + d ^ 12 *
    (11388369958625265353437010464822265165265846403072 + d *
    (-7147497871767267363209141999119341968196222320640 + d *
    (4034905588132052833058935732063404373584542171136 + d *
    (-2119215381340726053139192883642410582414361100288 + d *
    (1052800297013588367544127615562787121019716108288 + d *
    (-499248717188507187880292651172655095453520232448 + d *
    (227221153028780385488495303434678393717143896064 + d *
    (-99583694408605182653922647638029816857696927744 + d *
    (42112645753224551500670973211698756449541816320 + d *
    (-17203366820793386422196891713748974207267766272 + d *
    (6792041458783385631525011638574239089812307968 + d *
    (-2591537747817112988207377340642159167481053184))))))))))) + d ^ 12 *
    (955159391126907285043227833534717008620290048 + d *
    (-339756920803244304736998428451742924227739648 + d *
    (116486423131807902421759848564394465399668736 + d *
    (-38428917091706801180430503236017865824927744 + d *
    (12172436669597267397737796366708893260447744 + d *
    (-3691931651461054586897300562502571655168000 + d *
    (1068580490148573450075181349250826715529216 + d *
    (-293887876587340866893834897746846296047616 + d *
    (76391043625963941097542489241171797999616 + d * (-18639683065217930182941530039142976061440
    + d * (4232436128904602714608043783004099706880 + d *
    (-884167491791561023726817049980687089664))))))))))) + d ^ 12 *
    (167291639688614492525224243158481633280 + d * (-28019768671303846651380338346714988544 + d
    * (4002236709670810775052216959517589504 + d * (-453051718453762486335314950756237312 + d *
    (32866391254694385232244718705836032 + d * (337058226780554947196015602040832 + d *
    (-501070115523113079513127989805056 + d * (71197227413874816956609950908416 + d *
    (-4292161448107324202937886703616 + d * (239905756875180066205222305792 + d *
    (-169857212872464109935564685312 + d * (56480087835148168805224546304))))))))))) + d ^ 12 *
    (-9415986431931015539961626624 + d * (710637994687783970815868928 + d *
    (36733578474259618763112448 + d * (-14802429908490969696174080 + d *
    (1365462555517764243816448 + d * (-8494673279401089040384 + d * (-6864112468260314415104 + d
    * (181639183002058358784 + d * (11828171072965705728 + d * (4778488041877274624 + d *
    (-313076619349065728 + d * (-55748054535897088))))))))))) + d ^ 12 * (1599933042917376 + d *
    (345061824659456 + d * (16128697171968 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt16 (d : ℚ) : ℚ :=
  3361177382510976530624471627595555144728576 + d *
    (-152412993382532180540840370600236840187330560 + d *
    (-38243179269355844737180178104785669816582144 + d *
    (598025381488725699498574652412967155383926784 + d *
    (-982139650906571112029999371453033885537927168 + d *
    (664515802798638879721230433800455878143377408 + d *
    (1636377849432399141860994182883170337748418560 + d *
    (-5621783158102323388568543680946972077800292352 + d *
    (7998480673873654135909183093764408443944865792 + d *
    (-4615566656939414453075319615840881041794802863 + d *
    (-6851582746979689004212283539217263846833769350 + d *
    (23778746101156452394641966029293303846263680729))))))))))) + d ^ 12 *
    (-36441683960825431015200745383406139004536331285 + d *
    (31918151913235781406541276336691677221632593654 + d *
    (-2245191491056530217481354489621375385103659797 + d *
    (-48962574819215487707714488361098927329581667574 + d *
    (104046276334425635072276908581657282262046724918 + d *
    (-135855730739484180020037880771098581760979714900 + d *
    (119605135175826621921379049169018013357560087508 + d *
    (-45780401125482500518217636444497072770857958468 + d *
    (-72625508755717031302625317480131253703613977268 + d *
    (201691350987533058144395260841178031482492782209 + d *
    (-297411954450950757081031743769868994709494028960 + d *
    (322014076067828292167726237067944259754538254600))))))))))) + d ^ 12 *
    (-258416087621748492240388385403926097903024446447 + d *
    (116912972773168762739826958196590915794534627030 + d *
    (67964999060349466515808572907258948271484664357 + d *
    (-248901214368699322397216866057327988960131722514 + d *
    (380897707326158836917843837657430784444044308527 + d *
    (-434224448006307284160101667543973682751366922993 + d *
    (401154821325732234999519692357700627607592055115 + d *
    (-295365058945309367217175516020295825885487704264 + d *
    (145402664777211427176503095544047368107379809071 + d *
    (14729727407743512557116048758140981267641715753 + d *
    (-154521286925285265262663163622932755554866949184 + d *
    (253065526745775253355173524154869327575189662121))))))))))) + d ^ 12 *
    (-301445982004590049399740316570120121467592738004 + d *
    (301765728244972462232016731581222916072956412645 + d *
    (-263987067920578942377711644038501250479205711532 + d *
    (201979330227162441445653455133413339471325911165 + d *
    (-129919954418232272252520461005084361018607556162 + d *
    (59719890095868651552380663207914248041111004719 + d *
    (319323707895075556666267853181358383796224911 + d *
    (-45755048694830324219948833486280040393871069447 + d *
    (75486351629347899661848745408142413617532084789 + d *
    (-90837296588660995174588013041647116544193211589 + d *
    (94551408847125721282306361856793811001213950581 + d *
    (-89909885795255341255817337228697097273815882853))))))))))) + d ^ 12 *
    (80082979626098612377478334167478961916249480447 + d *
    (-67738233678942300461572976971843873337508323705 + d *
    (54872589966257471672859344699428643106956910346 + d *
    (-42808086361334269405114622365751398418903101563 + d *
    (32286203637776536271488706148317867194185142771 + d *
    (-23605524413115733294330615761418526342486197324 + d *
    (16763412535877780126597623577285175165280899675 + d *
    (-11578785718178393165485319204317836974462197096 + d *
    (7786224543550682765011434662577943031324309961 + d *
    (-5100544047165386936345037224043660005519650874 + d *
    (3255897774726326537149837618638562793063967663 + d *
    (-2025450539549920426793214365872179339462590015))))))))))) + d ^ 12 *
    (1227729357419463898565891940672549789256564708 + d *
    (-724853545079418550523491141806450783554363291 + d *
    (416579270825974948332535827152975560615880636 + d *
    (-232840442170242602485960210906695200541861831 + d *
    (126414553478994644867770234391041935624874306 + d *
    (-66554767509397325962372083806205855300380773 + d *
    (33899075443940230755107623916349655813169997 + d *
    (-16648737098525972564629479673264426420095247 + d *
    (7845791675494391151011999585077844153296105 + d *
    (-3520923293052605797165799690872704980808186 + d *
    (1485634051712693349090353486163176115372145 + d *
    (-575482750374471517800470152154628139221308))))))))))) + d ^ 12 *
    (193959364290316915252742723545975667374570 + d *
    (-47899393309754194513288847701819293237505 + d * (-171018856568154504322229839706792662567
    + d * (11215408600591719213777930865264095401042 + d *
    (-10400472996603508353344213410647756064598 + d * (7097534104751519857330407282302606631473
    + d * (-4215719052860666270652929010934912466620 + d *
    (2297082047695305836445244063098970996706 + d * (-1175173470543528246779144015000562345060 +
    d * (571369555558799586311488470971806472227 + d * (-265856167204078722182448221217672545531
    + d * (118879617156109821556395811100563627461))))))))))) + d ^ 12 *
    (-51213944034541306972588652726767333152 + d * (21286246858911625563380732165771433382 + d *
    (-8541014548957197323474327483286274614 + d * (3308472003541225069072778452645279532 + d *
    (-1236626520083484817240767279190237178 + d * (445568492045787122388783587110887925 + d *
    (-154527421066409340711518840832543448 + d * (51478946105829449868932070318892404 + d *
    (-16430812692428590202498370890347777 + d * (5008244188078083432476452999122396 + d *
    (-1451869073640180428168852368213373 + d * (398154625705790566870271353490615))))))))))) + d
    ^ 12 * (-102544854745540085269257147651938 + d * (24561215710254852656542501020591 + d *
    (-5399304324218917459762531282386 + d * (1070419417790350340833076941670 + d *
    (-186877946632590307997287343326 + d * (27760859484122901143343565219 + d *
    (-3317680739724950623716194002 + d * (284626223744283994962354124 + d *
    (-12082579341622342698745829 + d * (-434857655990032110344301 + d * (11695672262021070797205
    + d * (17900316581428443832293))))))))))) + d ^ 12 * (752778762778335135763 + d *
    (-1584852676843769851470 + d * (404661057126446374070 + d * (-52459298140998568089 + d *
    (3007116164708294194 + d * (126861002252102642 + d * (-31088297095895152 + d *
    (1199159025084080 + d * (14722347640256 + d * (10924174229249 + d * (-607729842277 + d *
    (-174429458035))))))))))) + d ^ 12 * (5041862215 + d * (1234320612 + d * (58451905 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_16 (d : ℚ) :
    orderSevenSelectionPolynomial d 16 = selectionExpandedAt16 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 16 =
      selectionNumeratorAt16 d := by
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
      selectionNumeratorAt16
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 16 =
      selectionDenominatorAt16 d := by
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
      selectionDenominatorAt16
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt16 selectionDenominatorAt16 selectionExpandedAt16
  ring

private theorem selection_cofactor_eval_at_16 (d : ℚ) :
    (selectionCofactor d).eval 16 = selectionCofactorAt16 d := by
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
    selectionCofactorAt16
  simp
  ring

private theorem selection_factor_at_16 (d : ℚ) :
    selectionExpandedAt16 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 16 *
        selectionCofactorAt16 d := by
  unfold selectionExpandedAt16 orderSevenDualKernelPolynomial selectionCofactorAt16
  ring

theorem selectionEvalAt16 (d : ℚ) :
    Internal.SelectionEvalCertificate d 16 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_16, selection_cofactor_eval_at_16,
    selection_factor_at_16]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 16 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt16 d
#print axioms solution
