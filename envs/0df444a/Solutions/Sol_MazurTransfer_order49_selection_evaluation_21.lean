-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_21
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:37:47.303039+00:00
-- url     : https://prove2.me/submissions/d5e47f9e-3c65-4130-aff1-a1678156b6fd

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval4.At21. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 21

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt21 (d : ℚ) : ℚ :=
  -13325807905979498496 + d * (-2158712352359055360 + d * (4492508374339227648 + d *
    (-9874381917935017792 + d * (14926367711659388544 + d * (-9278143291236094080 + d *
    (-1186330165146659904 + d * (8330281539439039296 + d * (-11815404734021537856 + d *
    (12088750222291062976 + d * (-8611999622033869632 + d * (3998010399377372928))))))))))) + d
    ^ 12 * (-282995223692771264 + d * (-2287170476292741312 + d * (3723706288545203328 + d *
    (-4003176476410282752 + d * (3515570626986348672 + d * (-2737076696256193152 + d *
    (1933143793960080640 + d * (-1244576265275478336 + d * (741732180632740992 + d *
    (-415110055879726464 + d * (216200121531843264 + d * (-103051787399687616))))))))))) + d ^
    12 * (45290435250073536 + d * (-18845671715774784 + d * (7384426105729728 + d *
    (-2577636230048192 + d * (771861132333504 + d * (-217078161198912 + d * (70370454262464 + d
    * (-24729627410112 + d * (7015300032192 + d * (-1374707364672 + d * (249524332224 + d *
    (-87606768192))))))))))) + d ^ 12 * (30799611840 + d * (-5694363456 + d * (371412288 + d *
    (-57326272 + d * (49407552 + d * (-10587840 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt21 (d : ℚ) : ℚ :=
  -15792829022179339200 + d * (-2743189469696571840 + d * (6839263818542752128 + d *
    (-15794805192297333888 + d * (25120157758051990464 + d * (-20923899734396345408 + d *
    (8571985472276269824 + d * (975326113891752448 + d * (-7470736049521319424 + d *
    (12143994599019086656 + d * (-12264592401251763712 + d * (9254649376747517312))))))))))) + d
    ^ 12 * (-5712736567671837888 + d * (2449716635395941056 + d * (92924827242099968 + d *
    (-1366862289367403776 + d * (1587187876247498816 + d * (-1339610203246019456 + d *
    (973230229167568768 + d * (-633856635947364096 + d * (388099298115581696 + d *
    (-233822905836448896 + d * (137418410311337216 + d * (-76734724792665856))))))))))) + d ^ 12
    * (41142601951258816 + d * (-21683014822028736 + d * (11129009046461056 + d *
    (-5433534500074880 + d * (2516203577377600 + d * (-1111552937900992 + d * (463033763617536 +
    d * (-178605718448640 + d * (63854397783360 + d * (-21388611657088 + d * (6573583478144 + d
    * (-1724981118976))))))))))) + d ^ 12 * (347120844800 + d * (-45176439296 + d * (1985746944
    + d * (389992448 + d * (-52109312 + d * (-1339392 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt21 (d : ℚ) : ℚ :=
  487916195846949529319965834894825852334215424973450510336 + d *
    (-22498904227463727233520752324263358344411042203124377845760 + d *
    (6943575724734893186475585169707851513438128206393772081152 + d *
    (45269578331657690807766106839869047413376689261978285244416 + d *
    (-88183601635860039092931108256470642887794399553411527999488 + d *
    (118189950580291794385514455706097954873097252365674396516352 + d *
    (-32943212523464424555514860876705920321134567035131413659648 + d *
    (-189152484233291722868486509853944127127508179757763574890496 + d *
    (415464797122027227918408053436821832044012279809180090761216 + d *
    (-494622317640648802352542586319715575122141555848791082926080 + d *
    (301484511518815328118703451164113666979488010564004585406464 + d *
    (193135734279116172127228555809123964984679198003249235099648))))))))))) + d ^ 12 *
    (-802689790446718729531927999365664996632188606322059031609344 + d *
    (1208151851295141478714849997117427999021118025188309609480192 + d *
    (-1148590312482768773913640115922558065292982634992506425049088 + d *
    (531784642128344347707199351812849998030612668100303645573120 + d *
    (494444189541668902576619831235085316329039086530859745935360 + d *
    (-1563507563624205972059837990087122223408837980308644756193280 + d *
    (2256313032054307854170201390141695892640379884287735140188160 + d *
    (-2286482990523605968038690244345967449943496963099701434384384 + d *
    (1604303727072196106956614828271412581664522943944766286462976 + d *
    (-413197453748870770729142749743043280747160422155125661630464 + d *
    (-911571423025656598924586703844765976511387436368975029862400 + d *
    (1974119850164852212600930786839625364665096027693737924362240))))))))))) + d ^ 12 *
    (-2496669455354068896433065733924550931400296029070408915353600 + d *
    (2392526272788668039657344691796425448817460449922954644422656 + d *
    (-1766027466604045945424142445064582961395292868271088401121280 + d *
    (850070313784421772997871511290313385284248123117087966101504 + d *
    (87898991150055460873654543178553053591802537118140187017216 + d *
    (-829705043683201982135759605525480329790862636424149084143616 + d *
    (1254528830353937174635254679824386311377780127452450686500864 + d *
    (-1346994577511628191282079031642980648424810685346754250145792 + d *
    (1173357280173367443007318633603555806302071313002628587716608 + d *
    (-841542604879399972452058434972106674217794966966592305102848 + d *
    (462195967257249361678073170940576579571436674912142009565184 + d *
    (-121695865261798740467982873813982389530864682878411903336448))))))))))) + d ^ 12 *
    (-129727135285361985146365114229334474986703079059472361455616 + d *
    (276874334901253975030956458477874343109418003750607654486016 + d *
    (-330386028444309434829224865289351062340014326445315468558336 + d *
    (314927454551136994275688406089228499121177658451203097100288 + d *
    (-258762512185967417761342982249224965513129956907684789747712 + d *
    (186652979466230548336665716497119333255285284309554924093440 + d *
    (-116382535308445242951319768888495284213345167680402126798848 + d *
    (58197103443935227188951732898444096642398827168509987127296 + d *
    (-16035090177885979477071790561277504542542011188323672391680 + d *
    (-10509054192790618224393398134214753238813708133217082015744 + d *
    (24228826793526745192638227575155585877124360263604703592448 + d *
    (-28758218282342132960838142195831146103498724580555954323456))))))))))) + d ^ 12 *
    (27563182468734191454820073869711337112342429099424582205440 + d *
    (-23425811033934359263878845610543109087285304571774949130240 + d *
    (18292339461515188625480646558993988106213260216692702969856 + d *
    (-13342872369071761522802761269815824061638553558967888117760 + d *
    (9164019267743932323979802174179067093841304606087110983680 + d *
    (-5942108856585227119556134226849459763831524554096786276352 + d *
    (3630762806686445994931952698312779486549987806804439465984 + d *
    (-2074697135437624065095853516465382574983102926851576692736 + d *
    (1089295242664209066886557060275049864648447236953743032320 + d *
    (-504245125922413669787031191055900796881229887671793352704 + d *
    (182120845046648753685543582606289426228423032780718604288 + d *
    (-21822299572630608386421480387189726850104300738804187136))))))))))) + d ^ 12 *
    (-45669590379622146699932878136232548530013754428732997632 + d *
    (64371150791403268199749522293278166429883355083356766208 + d *
    (-60477936337822493820243613003219182228449857913323782144 + d *
    (48396032572561257688624196368178313820485938335342395392 + d *
    (-35262559483424339437628856368520786592496543870568890368 + d *
    (24056765532080598417014478049176145777314760757060304896 + d *
    (-15587199051486994831767874565049459694291074669188218880 + d *
    (9670253310192129184877413855903556424654273288778022912 + d *
    (-5772915864732520330372136311422638330554420550627229696 + d *
    (3326468925375401002361293717789592286824487699375980544 + d *
    (-1853656681422478543001362750339083325787740527754739712 + d *
    (999987642322603268129685089811343072658684530158469120))))))))))) + d ^ 12 *
    (-522461047465899136107263599656416214162584881329340416 + d *
    (264316568626376339529709410149202069562819876719427584 + d *
    (-129377548345295123579198886331700515534265702799638528 + d *
    (61178453061371609446042321058393776466734031589343232 + d *
    (-27878369111530686057854734243972055449203143058653184 + d *
    (12194687536088697661445410849310068275061007916204032 + d *
    (-5088638913463946812327966216867547047567395431907328 + d *
    (2004577668261105750755195617102834560873523872792576 + d *
    (-731368954406048107630783848408448451265246358929408 + d *
    (237336455101188062800016318288987463224997789040640 + d *
    (-61195983490263503983635877602916627303512106598400 + d *
    (6339229335825277205853633097877336652140048809984))))))))))) + d ^ 12 *
    (6404748700512276617110160392405195775098905690112 + d *
    (-6674065221145340330943819373054274610486762536960 + d *
    (4448386501490187926590102880588405109199853060096 + d *
    (-2504304267742783500657919497493858638090886709248 + d *
    (1279224806592084405507972543339126353644789956608 + d *
    (-610502340087828194686120971421103879649764835328 + d *
    (276234454776789242411347366367564265860201447424 + d *
    (-119477540063252164883129257467108037378001076224 + d *
    (49639956240619655731508927716733571207905935360 + d *
    (-19869754843869481438890805274261700772441096192 + d *
    (7675623662854148540619030441872344504954257408 + d *
    (-2863935325622352502355727585905014332192456704))))))))))) + d ^ 12 *
    (1032330887876712511643692521252590470568869888 + d *
    (-359348255153479351095537724448823950107475968 + d *
    (120690504739840970032483287924329315231072256 + d *
    (-39058086794558691439129540734990876014280704 + d *
    (12157430601729107241900319936229337744277504 + d *
    (-3631100092392815821071117489857140896563200 + d *
    (1037458868771074448147818534794253299613696 + d *
    (-282438118865427436588438621180820265107456 + d *
    (72892923695477722316179903764465323606016 + d * (-17717843370311324826202616152543516426240
    + d * (4021593565606911224902546276631154524160 + d *
    (-842786833273322563569412342661265752064))))))))))) + d ^ 12 *
    (160522906566520033423476674666612654080 + d * (-27150450061192047015468802095529590784 + d
    * (3926140194351074603472150175952666624 + d * (-450511394481057670966952952413028352 + d *
    (32999042929531316758566917428477952 + d * (432098007314345990724761778388992 + d *
    (-546455771040274692416161424080896 + d * (79842393758746984733689706971136 + d *
    (-4993210640083523995378641534976 + d * (183797434595274361876252721152 + d *
    (-146894435052191633161982574592 + d * (53853442389368505662705762304))))))))))) + d ^ 12 *
    (-9361628846256532014494121984 + d * (729304396354532653428113408 + d *
    (35194018599167016687894528 + d * (-14852430355615572973322240 + d *
    (1368234240325419030806528 + d * (-7098428239999845269504 + d * (-6878568803867838644224 + d
    * (164522625992282865664 + d * (11729099073344503808 + d * (4874725554762809344 + d *
    (-306987785475063808 + d * (-55517627002912768))))))))))) + d ^ 12 * (1606526064132096 + d *
    (345133442400256 + d * (16128723386368 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt21 (d : ℚ) : ℚ :=
  26159926044659943927451607697813214358035834731 + d *
    (-1202503624761759302090121729268638086899953202665 + d *
    (190692292668773028444042724307346374680680715281 + d *
    (2801417776752766273709051371044228173519388912189 + d *
    (-4622426261525445940395179663508834030720083481228 + d *
    (4936076475880182899302241681144309254449625931253 + d *
    (938758385260929215256743857438680981956338949145 + d *
    (-12514328447665434580590087552257315229104351193822 + d *
    (21101546792979077295139409378652097996734580692072 + d *
    (-19236389818652653218973500955221040079252379864968 + d *
    (3976583268369636536722580705229889872959087888660 + d *
    (21386262463252031449678173674063448576032645913479))))))))))) + d ^ 12 *
    (-44458428784182055271668404800728477967579262023960 + d *
    (50775258760943777544711947610597395002670705011594 + d *
    (-33807200066252593779506556812615370888509638031907 + d *
    (-2725061828539210790698415299394880427683338847414 + d *
    (46165269257817097632104861250175372339618097199808 + d *
    (-79266504024700272807534453814189217317512958564130 + d *
    (88461003610896002058869372749700293941305533687213 + d *
    (-69863399606225177676246795275261269150882868145303 + d *
    (29652435694462034346984716072770417312643987150357 + d *
    (18958652029791716346531760600743155691153188863339 + d *
    (-60846459025156614803979891767277114611388182055805 + d *
    (84665069029880211679726599422574222687104701053980))))))))))) + d ^ 12 *
    (-86166608712708268982601707732143020481592144661122 + d *
    (68190768150606725216715794153276335738952663384330 + d *
    (-38442899804492603607454864297708587269741678910243 + d *
    (6247291904708202601223883057977432995000129791851 + d *
    (20540313876654884035306689439429934919315507406737 + d *
    (-37351275871379173867411082196601941626497184034963 + d *
    (43193928521443103480762624182095629645026576110370 + d *
    (-39870868286707769383847194328087607974349642908869 + d *
    (30691545187303744323102820334243107085690521313881 + d *
    (-19188859219117847983421486889173375780350395481087 + d *
    (8218052494513533272867548102757707970571044135956 + d *
    (444926012739294207121980036404118060881439257256))))))))))) + d ^ 12 *
    (-6099411413275045348520068833496919984320517628794 + d *
    (8869850595912777771870080532287142663138720630720 + d *
    (-9364467223845351105913402820039690232964342462947 + d *
    (8363796472606290369451913919742205032097016496150 + d *
    (-6601340696839852241524966565148366753653447419427 + d *
    (4645439465441483591344303788082088557204673830689 + d *
    (-2863823306036488986201732815355159427858037870369 + d *
    (1442700120148786356045699860120044028278949309463 + d *
    (-432264373861830982251926810237998230623337070446 + d *
    (-202633553719363237447424823231131349779855848329 + d *
    (538901149438223852180305854142825861375743623621 + d *
    (-663784306311174696256441062114713749260102235453))))))))))) + d ^ 12 *
    (656015184357473355833358708942672979432339544422 + d *
    (-577223437083425415985001081273901023552947805045 + d *
    (470325622409389765006788054310813390582027700231 + d *
    (-361833164173590054217971560654626282168389840318 + d *
    (265762518527143303982879556301176946163566072481 + d *
    (-187660920054243436625206474887551057675074861549 + d *
    (127982834482409154529643682557260000756558884860 + d *
    (-84567215572761710459594369526684938796572747696 + d *
    (54260338271240262771665213887885565542688417226 + d *
    (-33857788397646433475739044597798962177037260659 + d *
    (20567436116622932414507637004442591141635099138 + d *
    (-12171095543793439191950018675554812494322087195))))))))))) + d ^ 12 *
    (7018648875718130323101545618324641578835637633 + d *
    (-3944410561283580162404714888275494291638082306 + d *
    (2159933062018892360892726811729299768544947141 + d *
    (-1151988664607480038255876121049662823570072231 + d *
    (598016159873845564685637734546619932973357561 + d *
    (-301862362585990280981983020103511099901411188 + d *
    (147959473920382915362564406899130362412433557 + d *
    (-70289768668414054734148026617533344260420267 + d *
    (32277838080575570851398253933894356298187900 + d *
    (-14273164900712512915445627777453047580276891 + d *
    (6042902507455418730973940423708306919532685 + d *
    (-2427129027476070612850308558615800168345963))))))))))) + d ^ 12 *
    (910125787973274854463884749224247607890550 + d *
    (-308601160057605884453720987911240154991260 + d *
    (87352087936921358802772389186371126308103 + d * (-14751264582768926305778462155389862162133
    + d * (-4360960141095986564561990472903788025828 + d *
    (6592164974314433041939852159822394241313 + d * (-4787529065767123220853878029791803670660 +
    d * (2814128576759128650793515838165525587946 + d *
    (-1479335539431062857686720002988929674025 + d * (721723545206678243121798641849113463087 +
    d * (-332614592113706226022937619188955277371 + d *
    (146205703711184734967775467048902501616))))))))))) + d ^ 12 *
    (-61642090723964334433835087807406810932 + d * (25010474229534564287364387835132812547 + d *
    (-9784014517474114463190870722435974774 + d * (3693722710103090791265449772895871167 + d *
    (-1346038525703829823429791886542173588 + d * (473288560645028940356797751534591545 + d *
    (-160410556926465999872783697129488008 + d * (52319369098317298940942860266135549 + d *
    (-16384183225347331864016191353434332 + d * (4912133661717977306540574245772526 + d *
    (-1404923579433993875208165994461443 + d * (381559132972779717946899883475510))))))))))) + d
    ^ 12 * (-97765671086060120082686821310863 + d * (23413327030193766273099453371466 + d *
    (-5171398069876652853105629057266 + d * (1034263501727477879619243243245 + d *
    (-182628855762444521953131036076 + d * (27456342968055856392164973524 + d *
    (-3311693736237469937827898922 + d * (282926059637115725510937344 + d *
    (-10711082032553779358246719 + d * (-799784264067317332405556 + d * (62622216626322050074140
    + d * (15062460890849407285053))))))))))) + d ^ 12 * (451738596927481338568 + d *
    (-1514626772086437403880 + d * (400533693665227244160 + d * (-52611089445268661629 + d *
    (3018204372017717919 + d * (129562043255512407 + d * (-31062058677761807 + d *
    (1154220228942410 + d * (14232499169891 + d * (11225359865829 + d * (-587627707647 + d *
    (-173673518025))))))))))) + d ^ 12 * (5064097105 + d * (1234574612 + d * (58452040 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_21 (d : ℚ) :
    orderSevenSelectionPolynomial d 21 = selectionExpandedAt21 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 21 =
      selectionNumeratorAt21 d := by
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
      selectionNumeratorAt21
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 21 =
      selectionDenominatorAt21 d := by
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
      selectionDenominatorAt21
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt21 selectionDenominatorAt21 selectionExpandedAt21
  ring

private theorem selection_cofactor_eval_at_21 (d : ℚ) :
    (selectionCofactor d).eval 21 = selectionCofactorAt21 d := by
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
    selectionCofactorAt21
  simp
  ring

private theorem selection_factor_at_21 (d : ℚ) :
    selectionExpandedAt21 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 21 *
        selectionCofactorAt21 d := by
  unfold selectionExpandedAt21 orderSevenDualKernelPolynomial selectionCofactorAt21
  ring

theorem selectionEvalAt21 (d : ℚ) :
    Internal.SelectionEvalCertificate d 21 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_21, selection_cofactor_eval_at_21,
    selection_factor_at_21]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 21 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt21 d
#print axioms solution
