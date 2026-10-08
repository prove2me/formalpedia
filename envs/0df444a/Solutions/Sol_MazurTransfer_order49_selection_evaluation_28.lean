-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_28
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:25:11.954876+00:00
-- url     : https://prove2.me/submissions/d1e4dda9-d09b-4dd5-9eba-23866389a26b

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval5.At28. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 28

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt28 (d : ℚ) : ℚ :=
  -415775632792748032000 + d * (-45296753323297996800 + d * (67113379357876776960 + d *
    (-148479174435317089344 + d * (252986900184129234816 + d * (-167645239474045248000 + d *
    (22220679364408945728 + d * (52500400517519153280 + d * (-81694553271879317760 + d *
    (90251255210665058368 + d * (-66218212029363058368 + d * (35342994556869460416))))))))))) +
    d ^ 12 * (-14269119579936746304 + d * (649383869411987136 + d * (7727025484116619776 + d *
    (-10286304937073374272 + d * (9155174923212872064 + d * (-6961954639740386112 + d *
    (4754702714613230464 + d * (-2912044430431549824 + d * (1637590426724480832 + d *
    (-872943299312243136 + d * (435319926076926720 + d * (-196416120535197696))))))))))) + d ^
    12 * (80991426036452160 + d * (-32197815668343744 + d * (12390048350104704 + d *
    (-4232389781714624 + d * (1195581955735296 + d * (-308204154256704 + d * (96844939727808 + d
    * (-34583589561600 + d * (9610230025344 + d * (-1714450107648 + d * (271956878976 + d *
    (-101122423296))))))))))) + d ^ 12 * (36727309056 + d * (-6446516928 + d * (326140992 + d *
    (-42278848 + d * (50407488 + d * (-10571712 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt28 (d : ℚ) : ℚ :=
  -492758357243955511296 + d * (-56888909064313962496 + d * (104912719241750511616 + d *
    (-240506367032564183040 + d * (406755608236412573696 + d * (-328771923013337721856 + d *
    (145391188277098733568 + d * (-38623426544676843520 + d * (-19680581504982968832 + d *
    (70177261529393920768 + d * (-77840391492042169472 + d * (58523060930966879040))))))))))) +
    d ^ 12 * (-37913620120635840128 + d * (20306700328488279424 + d * (-6041289474871175424 + d
    * (-1354064065441336000 + d * (3123797572668289472 + d * (-2798574515583780160 + d *
    (2044044806058121024 + d * (-1283191330582497344 + d * (732930416822449664 + d *
    (-418142019165430464 + d * (235505078541381248 + d * (-122716102247505536))))))))))) + d ^
    12 * (60093386090107840 + d * (-29550981849479616 + d * (14508664193888384 + d *
    (-6722149821707904 + d * (2917881406735552 + d * (-1224057216204864 + d * (493694033588160 +
    d * (-183898494058048 + d * (62750890116672 + d * (-20289177129344 + d * (6237147172736 + d
    * (-1678219581440))))))))))) + d ^ 12 * (346602774016 + d * (-45664250368 + d * (1974801408
    + d * (399726592 + d * (-51127296 + d * (-1332224 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt28 (d : ℚ) : ℚ :=
  14833350916290660330160271554020377270983054552468439575822336 + d *
    (-689343440350634098340167382166371415808288118160704067141107712 + d *
    (369932550323934490718954193328846616227136581304242440809480192 + d *
    (752558973998889456451399386734791355156456982869603796964605952 + d *
    (-1373940957652582940414401137254485405258473379992431085030998016 + d *
    (2147639789993731010333556128444054354304982751375401901986152448 + d *
    (-1508920854336515290061364469919400800609702541750349494514352128 + d *
    (-831007693277583468854785953405443401467843223228183025656266752 + d *
    (3101155046228253370022456635390823165267809276704564421360353280 + d *
    (-4248776311164328402981611838629531339985056167142987744430260224 + d *
    (3749833232587601197582627522260106786475766794582865812076101632 + d *
    (-1360366302624648357405782013271435519799142419098571445561196544))))))))))) + d ^ 12 *
    (-1842757330002473705347874289716918983393784924433408800127975424 + d *
    (4244554478844408907862100937126861343742559577737198189570949120 + d *
    (-4987217694322246828923647944243176902036198833688279735623745536 + d *
    (3912271962036009012878157391521487819764663602553137198777237504 + d *
    (-1484078984975103160284328859240314771433717899075104942528921600 + d *
    (-1266052577785943059545049541285859394548914428828198371095216128 + d *
    (3331832151171879911413199932013103741972552712908296584897232896 + d *
    (-4191749017152924744679052414931029599829787143282218309081890816 + d *
    (3813179513143663325538898658283125181304444095744434907560017920 + d *
    (-2545655667002459985542510136234373618213323707937744693088223232 + d *
    (949842676983725620087662281092876663916950977159889201447567360 + d *
    (459143746451401329099434358218449316382394348683678994531876864))))))))))) + d ^ 12 *
    (-1375493323093232915993154509811526844053358852736087068997582848 + d *
    (1719393051332886765134919599546288782854085407246679873774419968 + d *
    (-1587046381686644732258526854179981251252708035372423813974458368 + d *
    (1170167302777525191880839188606086293721226674419563676428664832 + d *
    (-666427675875214265972708972683166634495487480765711212158648320 + d *
    (220700158538885242842758208851633439454722830715193848469127168 + d *
    (91936069175753986989856168094295393476595361492572022610853888 + d *
    (-257600887174230463745067850941200070368311538209284122436698112 + d *
    (302726816868892316835083648413146584963236508535660209540431872 + d *
    (-270196178923678484092636870673662824687212120119061264686120960 + d *
    (201289326488413314519424555790243568161079513131491237528862720 + d *
    (-126591985643440953028658372290444111974250170638995798136717312))))))))))) + d ^ 12 *
    (63808848236101161980657330742899750427479722648942869929000960 + d *
    (-19682536919887646825241671063612028797415376036624974125203456 + d *
    (-6265117784523589360990163157859194448915084740045510741065728 + d *
    (18044722761296827913002685349510972935098076257809657804357632 + d *
    (-20551935607343704326020119233009736386482959016046868457062400 + d *
    (18068479815180760876832608445642170033568425483996669472669696 + d *
    (-13662131260803677281061590182963525761482368428450576957177856 + d *
    (9172318029233194098022211203836330731932306140858737219862528 + d *
    (-5479076148090505938175283425288636153339486003776641683423232 + d *
    (2835676542432460449575615614233938634464855623592342503030784 + d *
    (-1154822679911400366603336793051232211328263772690081369030656 + d *
    (211963327755472095215956372952587985303122385143963527938048))))))))))) + d ^ 12 *
    (233863370134445683232448837827783962256011508437147696758784 + d *
    (-382980316625098304327656970924289383996038080881967710339072 + d *
    (378353674765672066628785080921876331955594635010340097097728 + d *
    (-309994602706585971944225756397770346046669817806726041436160 + d *
    (227694026398521908248700476613380942310295983983038347083776 + d *
    (-154657266348789844912582635781952380352591124317214222581760 + d *
    (98596496692166865097117520790002024086550036986708951826432 + d *
    (-59422209910045154371721576241245281204240694267980445122560 + d *
    (33936508267001600385163276050137093775560270194759959838720 + d *
    (-18333666409668535602091840906883436723835515637500868820992 + d *
    (9304947114195637684947835168864330285229971001475346989056 + d *
    (-4368387169241360035297817254316705496189984177317417320448))))))))))) + d ^ 12 *
    (1831902339371530004154761574575808136743632007111118946304 + d *
    (-623527646144628393319433470508839740553675217680289759232 + d *
    (105736607651205126196353207494223674888030136257740800000 + d *
    (78542989813428262960843887895883487200412202889797959680 + d *
    (-117143441389173093401646393445576401286736326311868628992 + d *
    (101944554058960527200461953382576344670588439922723782656 + d *
    (-73779894130404661749194795155437832082649929924525686784 + d *
    (48208029017683518794472911072179736469680931818957176832 + d *
    (-29375359160107981294467392682406959879076152673437483008 + d *
    (16962045729321793027154486651969610313494607621673189376 + d *
    (-9364451128927832689530064212260329720430680256210534400 + d *
    (4969520677305493935827952021066130387086473924117528576))))))))))) + d ^ 12 *
    (-2543314914716715314028981964779784606764483169106788352 + d *
    (1257749051094156691274953317820925403174237087604408320 + d *
    (-601653909051253638740047543111029235128756595682967552 + d *
    (278476251362541104368686562211219288098670521457311744 + d *
    (-124667161314484071405562959541251872589491238309724160 + d *
    (53919881681102342677856889366582885327080509685891072 + d *
    (-22484480563514321789702816803336984700808099719544832 + d *
    (9009237242866705320986608088223005246227498144104448 + d *
    (-3449912534563092728789716089310828192836666918436864 + d *
    (1251199747952863975280674658237895593166662526566400 + d *
    (-422893431245893063537227993313608799325443580493824 + d *
    (128905628159355490252830592702126664783985293393920))))))))))) + d ^ 12 *
    (-32590855940176531547626057870397145627864581537792 + d *
    (4732737974251333434209181838815299011251566542848 + d *
    (1514003835574299230808086668806534351352870207488 + d *
    (-1919454955500703304175444790319224698961499258880 + d *
    (1242415968931931972250435675046293055060654161920 + d *
    (-655891636864840676208746679520265904632016666624 + d *
    (310472997620122913278402564704171082734209335296 + d *
    (-136566988778281575584208945271917859146014130176 + d *
    (56784883929170158315900958820892285229899710464 + d *
    (-22528477236684496037008483096693547328199720960 + d *
    (8574316852775333590299273668283494385531748352 + d *
    (-3140738309403341191102134047294347334350536704))))))))))) + d ^ 12 *
    (1109187948483084269698794723813556033393000448 + d *
    (-377960525006971148826300264022520821060993024 + d *
    (124260102769959962774551953845306513662935040 + d *
    (-39387480093073897969519156839359756677152768 + d *
    (12022315961170242108628886707240659582189568 + d *
    (-3527308062880872381331100708674402186690560 + d *
    (992299444740169966441024190701244952084480 + d *
    (-266748182976718579794094615356052203110400 + d *
    (68205577985313460028146425828336783327232 + d * (-16487506244473217466262707023529658286080
    + d * (3737774238510622128924021329483496685568 + d *
    (-786060042156291367484562123860734902272))))))))))) + d ^ 12 *
    (150994287267812459794210079974976651264 + d * (-25882056804428241345872260801991278592 + d
    * (3809170263873664144423575462789775360 + d * (-446144525179723010648465831688404992 + d *
    (33304574243692528295152977917771776 + d * (519565103675021953061114095337472 + d *
    (-603918682093294064784988873949184 + d * (91734718907315479635417953730560 + d *
    (-6028483883913440459179734859776 + d * (112897497965727549869223051264 + d *
    (-114813881029427210762658512896 + d * (50127481433466144003404595200))))))))))) + d ^ 12 *
    (-9286475881624420582593658880 + d * (756031034497636955350106112 + d *
    (33063803068103550043684864 + d * (-14929433177161277796515840 + d *
    (1371820592005895414874112 + d * (-5107303386171067334656 + d * (-6895418477980415688704 + d
    * (140705153393253679104 + d * (11594640677527093248 + d * (5009512011468111872 + d *
    (-298463315481853952 + d * (-55195028456734720))))))))))) + d ^ 12 * (1615756293832704 + d *
    (345233707237376 + d * (16128760086528 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt28 (d : ℚ) : ℚ :=
  343276953477860372544926488683541939316718684864512 + d *
    (-15915775584884224419655929076028934775282817803747328 + d *
    (6764293024942026268320142564042874527426899980845056 + d *
    (21595799833474706832231748140132436491607188829110272 + d *
    (-33437921746420526528531511255092409632790655340118016 + d *
    (43016666244581648551133593831255647601490374886948864 + d *
    (-19122811386703858184530801620361729039543784717680640 + d *
    (-37309876665277248319957538851590909389275053979148288 + d *
    (79014728214259665619225339660081477707407815220806592 + d *
    (-83935204451710069954327790301263344563504515268262563 + d *
    (52069284485936580387877777386333656888413306953241986 + d *
    (8565174636220003914809294252747156059512776590809893))))))))))) + d ^ 12 *
    (-68014023682802295299901044170330168050693582861440985 + d *
    (95163979857291246816334854860737057347167223169763986 + d *
    (-83770708416429810123076695498470263799771771965918565 + d *
    (43740456656067395727482782279047176067999185760469202 + d *
    (8051315349660209197512923591253896362332580374180942 + d *
    (-51339840378601865409111711957484540847104526395658272 + d *
    (72592166485950989201068181313388644877542602183890528 + d *
    (-70227801860608968860118859130499572016186558209157804 + d *
    (50479814747123193384921279800197600316035476808052472 + d *
    (-22923776053288358203503291262018625418177497932450511 + d *
    (-2773850428250775911189080679938978367172752695015660 + d *
    (20277711923095587933367380985693401791946847274021368))))))))))) + d ^ 12 *
    (-27803209718667027489202649102461460655368352153188687 + d *
    (26871821271134312240227413800859524401883705094913650 + d *
    (-20641982912135458023225278977768181387564431398659603 + d *
    (12521017074051283596135335565237383496240160321344218 + d *
    (-5092797805932783712482268618224010666288350514110253 + d *
    (-296180923213571515626130507271092955949457336975825 + d *
    (3347789233102023870994908534878125223351448678657751 + d *
    (-4425355749288803878228834578697544158238029145576104 + d *
    (4183412659545361298293393534890479950919844172992799 + d *
    (-3275697409762518199512304093532541397995174345960091 + d *
    (2194309337898118176000487799369316687284632660818308 + d *
    (-1233750241532335208215016689302201585860775186758239))))))))))) + d ^ 12 *
    (521509612500699649624413934058547126026968635555696 + d *
    (-71051489980885328987445148249358261514290151674659 + d *
    (-164300187839068845341461881693801264376921008930720 + d *
    (250286038797879391967676397389838381283682292325105 + d *
    (-248057037512535746400865180995821555061430257328306 + d *
    (204106844277122026355993104958967360651895274889887 + d *
    (-148487225670811094224314487562098581217444396857841 + d *
    (97452090465274644047462059395540847050722440490177 + d *
    (-57648501735502622999415082341162806637699576539135 + d *
    (30018884652438931232024946083224379320231349484987 + d *
    (-12722942350247870847138043285340617939507964900723 + d *
    (3028411570723100418247391254432404576102411199519))))))))))) + d ^ 12 *
    (1660391209213299800036936071434783445677883853087 + d *
    (-3381422488709806413514205786537063953184150889269 + d *
    (3545070708635746209323379126811538497304987403334 + d *
    (-3027812010727420873398619023396439516978183449555 + d *
    (2317077547766191246791093768169260613361194319239 + d *
    (-1648257724354833951716482074950033070461567044024 + d *
    (1109989090079004728981350124478413219101243206663 + d *
    (-715087118580954428432616773118965785530795577972 + d *
    (443574674426598361991353449734891665849910297385 + d *
    (-266068240931544175936325846758375158930225305966 + d *
    (154772605067591084025225597389377935381429554691 + d *
    (-87483969237268815582340449614518545319600471751))))))))))) + d ^ 12 *
    (48113847882732285702052362483022830614624623108 + d *
    (-25768249654323783256222575071589805366805960339 + d *
    (13445669147896931046592473905054017234219164164 + d *
    (-6836624965903762897729422350473905102140290299 + d *
    (3387058765335237719340855079174320030134227198 + d *
    (-1634448784442113726072448253689928498141422413 + d *
    (767744286012743910245927754493171659712232601 + d *
    (-350712509073699776988245349959851980737668399 + d *
    (155594883126485874334164902599258856699333977 + d *
    (-66917714606939507726696929635820187375702730 + d *
    (27826465644914895591609213711019835656529017 + d *
    (-11145826412336836735236314203343221471002692))))))))))) + d ^ 12 *
    (4275921457342185009689381087619777333105598 + d *
    (-1556836254012801582135539686069365954749389 + d *
    (529474963459211215550776702524409696150889 + d *
    (-162975691278514712722359386427390421124506 + d *
    (41964342344740275264747823730453600000914 + d * (-6514201100263926915422577482902347767407
    + d * (-1657618530883377190645234341327456569572 + d *
    (2328116194815905445488701472298263168414 + d * (-1541343500736961037427423818081066250816 +
    d * (824262570805066876680075447145756818067 + d * (-394026803677326775589914263910420677431
    + d * (174804711859200803202652720228716107565))))))))))) + d ^ 12 *
    (-73261058212629367831413983588171894604 + d * (29284519014029464184768178621929127766 + d *
    (-11225658063854850973478483079361562538 + d * (4139589771054447112528519100423542016 + d *
    (-1471071282387836510877146416600472306 + d * (504185536937190195228585691924366945 + d *
    (-166655608940177136460755233532855940 + d * (53080041705070270628678689748587212 + d *
    (-16260646365366144256080965396710249 + d * (4778951725875005639843065705235256 + d *
    (-1343388924991597561536138078427469 + d * (359910004616475140605899297416543))))))))))) + d
    ^ 12 * (-91444876324395104989941723020030 + d * (21860056933207186453782674051043 + d *
    (-4854217802425573973676248122158 + d * (982272836877504908012407043222 + d *
    (-176264077669229139207703389946 + d * (26969735216592522857965215211 + d *
    (-3300527617407517321193833954 + d * (281270946483045966432433780 + d *
    (-8959175850728989191886289 + d * (-1297675398286234458618417 + d *
    (134334388732215411960165 + d * (10965392097194815321593))))))))))) + d ^ 12 *
    (28669284671388391627 + d * (-1415241432988421326998 + d * (394829790274104916286 + d *
    (-52838616634775627985 + d * (3032873049684472198 + d * (133439264743713986 + d *
    (-31015378732779052 + d * (1091743387780640 + d * (13559735222168 + d * (11647193899205 + d
    * (-559484342593 + d * (-172615202011))))))))))) + d ^ 12 * (5095225951 + d * (1234930212 +
    d * (58452229 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_28 (d : ℚ) :
    orderSevenSelectionPolynomial d 28 = selectionExpandedAt28 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 28 =
      selectionNumeratorAt28 d := by
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
      selectionNumeratorAt28
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 28 =
      selectionDenominatorAt28 d := by
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
      selectionDenominatorAt28
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt28 selectionDenominatorAt28 selectionExpandedAt28
  ring

private theorem selection_cofactor_eval_at_28 (d : ℚ) :
    (selectionCofactor d).eval 28 = selectionCofactorAt28 d := by
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
    selectionCofactorAt28
  simp
  ring

private theorem selection_factor_at_28 (d : ℚ) :
    selectionExpandedAt28 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 28 *
        selectionCofactorAt28 d := by
  unfold selectionExpandedAt28 orderSevenDualKernelPolynomial selectionCofactorAt28
  ring

theorem selectionEvalAt28 (d : ℚ) :
    Internal.SelectionEvalCertificate d 28 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_28, selection_cofactor_eval_at_28,
    selection_factor_at_28]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 28 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt28 d
#print axioms solution
