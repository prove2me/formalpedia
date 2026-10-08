-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_34
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:02:51.915035+00:00
-- url     : https://prove2.me/submissions/89548966-ad17-4954-8967-fb58d2e444a3

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval6.At34. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 34

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt34 (d : ℚ) : ℚ :=
  -4246214230702074068992 + d * (-357765275543090835456 + d * (396418209015685142016 + d *
    (-884921869151455354944 + d * (1699555193847070296192 + d * (-1141113137281678379520 + d *
    (227972074715083802304 + d * (157241344909903871616 + d * (-277367515307705236608 + d *
    (342478383122036663872 + d * (-254342685978929824704 + d * (137048475859917448896)))))))))))
    + d ^ 12 * (-66226473586141471680 + d * (22595659646930066112 + d * (6978013485577333632 + d
    * (-17987149907750444352 + d * (16966371273568010880 + d * (-12921992512201933632 + d *
    (8768208583948400512 + d * (-5232235557721545600 + d * (2829523922429694912 + d *
    (-1464727951270122432 + d * (714237441560605440 + d * (-311019774088555008))))))))))) + d ^
    12 * (122094363848256192 + d * (-46922087693854656 + d * (17957825802131712 + d *
    (-6083243052846272 + d * (1646774641862784 + d * (-394089565346880 + d * (121045742529600 +
    d * (-44211688535808 + d * (12160777517184 + d * (-2016914209536 + d * (283078881408 + d *
    (-111789705984))))))))))) + d ^ 12 * (41925184896 + d * (-7088614080 + d * (287337024 + d *
    (-29381056 + d * (51264576 + d * (-10557888 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt34 (d : ℚ) : ℚ :=
  -5032461399624296595456 + d * (-446069973736044832768 + d * (641142777556339591168 + d *
    (-1469658802728859499520 + d * (2672390735018532319232 + d * (-2102698704438457950208 + d *
    (910313753947868645376 + d * (-332017190480913957376 + d * (69468710160281289216 + d *
    (201755760137441287552 + d * (-263855048504938394240 + d * (197291884416172117440)))))))))))
    + d ^ 12 * (-129218599878796634624 + d * (74383152054703934080 + d * (-27411386817120914688
    + d * (2460682369220754368 + d * (3947775553362484160 + d * (-4127405490337173952 + d *
    (3217743747790790848 + d * (-2037645214170653120 + d * (1111482328277619968 + d *
    (-614395794642331968 + d * (342630685275199616 + d * (-171500229574978688))))))))))) + d ^
    12 * (77951552411588032 + d * (-36325695299635008 + d * (17495330773708928 + d *
    (-7869552957145728 + d * (3241603387731520 + d * (-1302803804089920 + d * (516449833618752 +
    d * (-188870871069376 + d * (62087680690752 + d * (-19371931010432 + d * (5944376882048 + d
    * (-1637511308288))))))))))) + d ^ 12 * (346260230656 + d * (-46081016320 + d * (1965419520
    + d * (408070144 + d * (-50285568 + d * (-1326080 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt34 (d : ℚ) : ℚ :=
  15806434315856144926559892964236609927751077961416116441964347392 + d *
    (-737025537492086815402661389028158647982079899260338224357372329984 + d *
    (469581116559696452736100376037103588398406910238010018672614047744 + d *
    (531904752554312417281207567035669891329525605509970981514396041216 + d *
    (-893990579737318169338641809189084517253314408285034129963333189632 + d *
    (1525750667188031892884261203235534513304439925602502036349691887616 + d *
    (-1298049955596587653698786009902228453209445358852596179705463308288 + d *
    (-8802786248466710991520670201073946923694752323110412660114456576 + d *
    (1177897370919935283946040036214236350823122344237536062491710193664 + d *
    (-1778435593208143399002545357512187760668628914007210478929878712320 + d *
    (1764185662949129404895987988836852290241349708680812752681140224000 + d *
    (-1004236069524642840911925903432671590463440001908201210381565689856))))))))))) + d ^ 12 *
    (-89987156920333929298333208285984339659900248645861985202046238720 + d *
    (910907950298552504991143595276016861740764580497196032669512368128 + d *
    (-1255599410625593139076194162952858042520009402054885784182915596288 + d *
    (1135378374628957863524227899600140291318848182611031339632769105920 + d *
    (-663502032140572617571289151482676333328911492107653000500082900992 + d *
    (90724680615893588288303570520204891587456135317643884187633057792 + d *
    (354885988701999652556257231890352339954580800503378368097504722944 + d *
    (-583513617390107806118973916642714111535583639730232730821865504768 + d *
    (600284002631322088153315587100594200662105056549258705246949474304 + d *
    (-464375951785772387340335298118282885503598224689972286177322205184 + d *
    (265643877211155499046742211393282175113586663010228430395706703872 + d *
    (-81246561560107856159305410546529692000489021431748069383247233024))))))))))) + d ^ 12 *
    (-48580384469938759924392243513319012689726819114735561240081072128 + d *
    (114451353012633323326696413542898809116260592708617657480479768576 + d *
    (-126761520087611838736274397820700716488389805332656985640416313344 + d *
    (105944566094004275926055723147290404851784794847881283068549398528 + d *
    (-72147322735083019952519455770796827120576121746794569434017038336 + d *
    (39212992196374428694178122944697413240874267953765672183898308608 + d *
    (-14167027520365234337122519789674105790909843101531300304791797760 + d *
    (-1195301006804084096367636320291462003633175728170189200362569728 + d *
    (8329890669646736318918257563063021675121424530976120137585262592 + d *
    (-9943323271097519901075849601360683366334959925446210723133259776 + d *
    (8607654643337964184108479781019277261148590933432750740387397632 + d *
    (-6200968316104752660310999648496663070052663843580185499960606720))))))))))) + d ^ 12 *
    (3837736067693494679734314158893439160073552597056221888443056128 + d *
    (-2009273308511585803490114712183588244945753939960242195456065536 + d *
    (807880266876726088762005541291643437166967934438009422422736896 + d *
    (-132953826522686115563998914865524415818621784095036339664715776 + d *
    (-174967715519318231106401820690654940844383862126019074621702144 + d *
    (264589923168138901332258668618270248401928048337766825506373632 + d *
    (-245890638617714290687033144526852285519821000703462552572526592 + d *
    (187443632156973598763381569132123069199173757623539272798699520 + d *
    (-125557490576402897490097578005524599601864657893958664348499968 + d *
    (75494033515938110223328828921905575573205881024204857141624832 + d *
    (-40679535113192166080839333188327145650984294858406683155890176 + d *
    (19104755310477070968858853570543189427804136122853697878228992))))))))))) + d ^ 12 *
    (-7117430085839461431102890230932608610383383797133291684364288 + d *
    (1252642863013820393300961827905168811407176562246931693436928 + d *
    (1116760228706996327689954865971012613804359343919438468481024 + d *
    (-1719127746540593550232632220207281972934328751336378725040128 + d *
    (1564930407230989497277188408103209562309724712115378599493632 + d *
    (-1179239893465591823604617103311367189202769041624990734090240 + d *
    (797072195468475838587795069096263221842662930847386777157632 + d *
    (-498882838606183599214876903087304154917265965397047477796864 + d *
    (293548965876584222873401696543796725143361564563890478776320 + d *
    (-163586845782210591988287039991722764349476290088180239826944 + d *
    (86576003489763088832050285770400916646152498299194631258112 + d *
    (-43467580995921954373503643338924682361325731964140338282496))))))))))) + d ^ 12 *
    (20588918773812098845846650485880861674479243760147902758912 + d *
    (-9084349535192752652750822508145311694071894142128729096192 + d *
    (3632829388873312276022747918342135056194759902581487566848 + d *
    (-1229178544196584817084894864557213848221369149871644475392 + d *
    (269983384850385768293867218317256464216275855110978666496 + d *
    (52935938785411399824639061950230676049144857232780558336 + d *
    (-122581903365007754842150897379268265966706756464485072896 + d *
    (107484075997306397733845787313164404399867970477657423872 + d *
    (-74520729146335865241911583799591190243799949044805271552 + d *
    (45900113034845785843601944956781841725219423725596442624 + d *
    (-26175515143331896042607902260775625193186838344216870912 + d *
    (14090187610378756909145562744286671144386796605405659136))))))))))) + d ^ 12 *
    (-7234756709610540948136116695447240284691066475212963840 + d *
    (3565155076828710284419454410838859950809846653171793920 + d *
    (-1692341158835593177662753771421399864805144061232545792 + d *
    (775556884403409053622415867670953721947267518017830912 + d *
    (-343538723841620668932010916629327770552575888319315968 + d *
    (147141394121840561811778501279875516884490227418398720 + d *
    (-60912462280340114558350069278402126173152449442349056 + d *
    (24340924449946536110256608540782142069795979114840064 + d *
    (-9367727299707227838437443027639696493542927078260736 + d *
    (3459171185125532444182113557523700659493123786014720 + d *
    (-1218086081253107246782769272842977560153616786653184 + d *
    (404737651205833787701694890483107955432207887106048))))))))))) + d ^ 12 *
    (-124446795568700674860497047241326351145491661324288 + d *
    (33962886462808026527695120076410672453612832292864 + d *
    (-7312459759968424781436031746230194449896960163840 + d *
    (581659506841180815978674896317586287536884678656 + d *
    (590229230633097859908372515268315868947173605376 + d *
    (-505481657208134564883436084487067508198447251456 + d *
    (282838628690107112461297262394720164558549286912 + d *
    (-134230216422592813620564457152966788660375060480 + d *
    (57883094205792601651976298159200143208277868544 + d *
    (-23330245665789108147221611222687946929864966144 + d *
    (8914452890866165738599718733426798302837342208 + d *
    (-3254633932025792729895369185944604056517869568))))))))))) + d ^ 12 *
    (1140603911263712836119207648493434866892800000 + d *
    (-384676600717519839784479914426721029891817472 + d *
    (124986484068884286904405245165824273949392896 + d *
    (-39126569772129433774892999878230232879595520 + d *
    (11793781355381319924747987203374227523895296 + d *
    (-3418936928190400685864362580065467270955008 + d *
    (951409671842260397229520378559087610691584 + d *
    (-253415003591664020228010122728656393732096 + d *
    (64339525097566255031569305862554749501440 + d * (-15482586979403564819041770707210634526720
    + d * (3504783314838881417984098697494121676800 + d *
    (-738701911835909354994798433353655648256))))))))))) + d ^ 12 *
    (142823838910743802442369397156758945792 + d * (-24753803809459890017120646825125347328 + d
    * (3699521321284417967958324533242888192 + d * (-441575527081413823494931295840763904 + d *
    (33662735482451633705817900980371456 + d * (552896490558660225660672959053824 + d *
    (-647423913608603071693397625667584 + d * (101721945445448068110152544813056 + d *
    (-6966882871256015608675805429760 + d * (59352444380571612577419755520 + d *
    (-87364203024996051165462396928 + d * (46887181221251050453282586624))))))))))) + d ^ 12 *
    (-9223080872490880676970364928 + d * (779497366442851472275144704 + d *
    (31262361476971618636398592 + d * (-15001881461091281659756544 + d *
    (1374623337000662170599424 + d * (-3366817144921976209408 + d * (-6906713871964209152000 + d
    * (120425476416024084480 + d * (11483329998789279744 + d * (5125093345976385536 + d *
    (-291156531673038848 + d * (-54918515417153536))))))))))) + d ^ 12 * (1623667919290368 + d *
    (345319648526336 + d * (16128791543808 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt34 (d : ℚ) : ℚ :=
  206813771051986114375192471054690506315916480838893568 + d *
    (-9624940533600169751504229665143712657866016139939676160 + d *
    (5250817813955743147455332447655338042270536924639789056 + d *
    (9145692471656857677093364353607235507194410367853428736 + d *
    (-13096325838616121514217937860880517469726162428590497792 + d *
    (18181112728806232467621827576228961155355172488317078528 + d *
    (-11692308630115141888194777769541959474680894317537180672 + d *
    (-6753647632157251008988809065342813159431818774285833216 + d *
    (19574327955074842906106274112870295173160437898691817448 + d *
    (-21898312678552459567166712637027804390213632650596849569 + d *
    (16250175622825495331482494144007360434264545628034792638 + d *
    (-4169985890574656301921481650878473628014456527800388949))))))))))) + d ^ 12 *
    (-8104798641864019326867039915728813845473693299330601711 + d *
    (14119837457203041503726984497564372094542652243291071612 + d *
    (-13680254212275562087450685090615514498407683590543331577 + d *
    (9092624486479524695021567444977315986992698850023854686 + d *
    (-2679236487496791495201329315268764816672261287920454938 + d *
    (-2895092802466721273840061842912299278882131183407521202 + d *
    (5940598951750959128111075104359353540538427070349775462 + d *
    (-6467695480510390549115439006472348229965440211081954512 + d *
    (5250657351141717005539928429904679180124946016677954150 + d *
    (-3194607836214877350507341114476509747878428546989085271 + d *
    (1165511241818625220685140377197870998326554780208978710 + d *
    (295117919345176403794919711900234834479384029153309736))))))))))) + d ^ 12 *
    (-1063852191837952003257513395362780322992154537901648839 + d *
    (1259936404797394730594665335558044742851749661579382348 + d *
    (-1089118870284864902828579846303842717161713021087478059 + d *
    (762322184277981777166158351978801224815170736067655188 + d *
    (-433554030996219481821038225370159152360112571144239139 + d *
    (178973134742163835957808748410579869898667416088250991 + d *
    (-17645916737598884472962582141206430415847460659195895 + d *
    (-62433628138179860839508488678597622548595540498849860 + d *
    (86353153865929978368749584022179518843457963659693871 + d *
    (-79323087423905287546474473286330684002727305710202457 + d *
    (59858891003799888319837342119735121826146624663952702 + d *
    (-38998218037560276468092147643355978841808795087644587))))))))))) + d ^ 12 *
    (21994662157205825655526293699575242434718803617131062 + d *
    (-10284258626466945749231224729317729600298213281807259 + d *
    (3284706307859625211719607016920239027551292831180618 + d *
    (279367852575470252351318869175581521428278162182575 + d *
    (-1676051403902015369134687518409093804487580838167310 + d *
    (1896690358231735415459497574506831140277565657243747 + d *
    (-1599284064260691499517501923350813322097588459860633 + d *
    (1158157556659485163857101703385553994459997398507713 + d *
    (-752180642230762019028858870433517364573288449040809 + d *
    (444375219425785736525815361799551317988396117363007 + d *
    (-238230938737900744983931820572682855821508285965079 + d *
    (113246979449037259520799847125150654554893417184077))))))))))) + d ^ 12 *
    (-44388447578451085884411479262870268564294297616953 + d *
    (10431934684560730727491312496111583929346372720289 + d *
    (3831900506988226074580313002520284945690296846484 + d *
    (-8096618908119177980068637708059734104149150310103 + d *
    (7943008493564143138489774166265070198171918262689 + d *
    (-6275058865270837888407696443475366335843016616750 + d *
    (4428144950085493973378214655589298835015678830189 + d *
    (-2902163987028245872238555554334504550909366654934 + d *
    (1800378384068221802260312789901810774636781145665 + d *
    (-1068504072411506646889873448660607123014446093376 + d *
    (610691291160593006946922793646942496451670555189 + d *
    (-337576037735332962897607609533840210300823464791))))))))))) + d ^ 12 *
    (180992921942104752808180511747933277154507287976 + d *
    (-94299650395850196230713766132166608766288853907 + d *
    (47804497395984399738580673797056320119014012200 + d *
    (-23599092436135773579661981449145295316280087989 + d *
    (11349512282887867947905470491372591642093866740 + d *
    (-5318113772267244925117972994324479057090197049 + d *
    (2427531108935513782335405930166889018051800491 + d *
    (-1078980232527347774874898240424312467637107651 + d *
    (466639600352004943581929256798992537860967425 + d *
    (-196151509779360129169247238674790242778266574 + d *
    (80018090712512197223087298959811693539096689 + d *
    (-31612584960258877477367752341975275609398028))))))))))) + d ^ 12 *
    (12058102716954092505108076097045493021363616 + d *
    (-4420345233481683518081839684978266168144919 + d *
    (1546460601740557729731276114332566900254917 + d *
    (-510422454038527224626978154630170201778820 + d *
    (155614065549219677882894112529498475856430 + d *
    (-41848315043530725774735768485337291619999 + d * (8660176346984192656870520145756573633212
    + d * (-442818940577954163170995915348708472680 + d *
    (-885742048799813065570718989163542352334 + d * (702880784962294148049101278775593098655 + d
    * (-385699475600023030014845539632305069465 + d *
    (181683193221811345924014830786237188917))))))))))) + d ^ 12 *
    (-78128071724445610171000306388552193282 + d * (31477300226587026014769216578224729342 + d *
    (-12038035378916010375762679355936555508 + d * (4401406012357088806620444330724881386 + d *
    (-1544856915112066442398704812494394090 + d * (521788543760643188099063862898620307 + d *
    (-169810553188143416642159231837746078 + d * (53254173208322980564854578942589816 + d *
    (-16074596571174252474560375862218089 + d * (4659067798907682730340549293127226 + d *
    (-1292934716738840914972172430571817 + d * (342540774933986544170367243309863))))))))))) + d
    ^ 12 * (-86337942774783213745954201439756 + d * (20578314408122296838578678822389 + d *
    (-4584914836187179019394779402892 + d * (936615217054913352252005589506 + d *
    (-170438882817781957458077685712 + d * (26496218909715991983159453031 + d *
    (-3288106254394774881721219570 + d * (280511450431991716795385368 + d *
    (-7615930376194190423193359 + d * (-1712196097378020106114983 + d *
    (196218779719846086037221 + d * (7336098801015655077795))))))))))) + d ^ 12 *
    (-335794093382789303741 + d * (-1329048243828659158134 + d * (390012582040876904342 + d *
    (-53047435210823773353 + d * (3044657276280817012 + d * (136851593403670178 + d *
    (-30966131395712494 + d * (1038598034898716 + d * (12995174041280 + d * (12008927631251 + d
    * (-535361108587 + d * (-171708073999))))))))))) + d ^ 12 * (5121907819 + d * (1235235012 +
    d * (58452391 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_34 (d : ℚ) :
    orderSevenSelectionPolynomial d 34 = selectionExpandedAt34 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 34 =
      selectionNumeratorAt34 d := by
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
      selectionNumeratorAt34
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 34 =
      selectionDenominatorAt34 d := by
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
      selectionDenominatorAt34
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt34 selectionDenominatorAt34 selectionExpandedAt34
  ring

private theorem selection_cofactor_eval_at_34 (d : ℚ) :
    (selectionCofactor d).eval 34 = selectionCofactorAt34 d := by
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
    selectionCofactorAt34
  simp
  ring

private theorem selection_factor_at_34 (d : ℚ) :
    selectionExpandedAt34 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 34 *
        selectionCofactorAt34 d := by
  unfold selectionExpandedAt34 orderSevenDualKernelPolynomial selectionCofactorAt34
  ring

theorem selectionEvalAt34 (d : ℚ) :
    Internal.SelectionEvalCertificate d 34 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_34, selection_cofactor_eval_at_34,
    selection_factor_at_34]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 34 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt34 d
#print axioms solution
