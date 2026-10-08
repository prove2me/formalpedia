-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_14
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:52:57.707612+00:00
-- url     : https://prove2.me/submissions/f8d08355-8948-43dd-b6f7-e0227a8fd985

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval2.At14. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 14

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt14 (d : ℚ) : ℚ :=
  -105132662185951232 + d * (-30838926121414656 + d * (92075558369604096 + d *
    (-200831444145955904 + d * (266358269252030592 + d * (-110138984235471360 + d *
    (-212526879376289856 + d * (515571754812894336 + d * (-689374516093193088 + d *
    (655338058903953472 + d * (-380258694226567104 + d * (-27617849054662464))))))))))) + d ^ 12
    * (433707612848609600 + d * (-756772505714879808 + d * (947352921725469312 + d *
    (-987067468217447232 + d * (904531715559749760 + d * (-750238986018384192 + d *
    (569542907716200832 + d * (-397971956468484480 + d * (257961691208356032 + d *
    (-155801171431384512 + d * (87230824817905920 + d * (-44952660688201728))))))))))) + d ^ 12
    * (21376485212102592 + d * (-9447707646415296 + d * (3843813637066752 + d *
    (-1396943952711872 + d * (449135948006784 + d * (-138251840185920 + d * (46659317133120 + d
    * (-16394716670208 + d * (4815763611264 + d * (-1049576468736 + d * (216907832448 + d *
    (-72938275584))))))))))) + d ^ 12 * (25018905216 + d * (-4938936000 + d * (416683584 + d *
    (-72373696 + d * (48407616 + d * (-10603968 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt14 (d : ℚ) : ℚ :=
  -124589087298256896 + d * (-39905749570541568 + d * (138517329128450048 + d *
    (-326028241196743680 + d * (498799910507077632 + d * (-407009252976539648 + d *
    (56225184985993216 + d * (334164532492639744 + d * (-669934147230897664 + d *
    (883263071753537152 + d * (-849807164685235840 + d * (604093076408038080))))))))))) + d ^ 12
    * (-264637932379762944 + d * (-82680971087699840 + d * (356895883020084992 + d *
    (-494651073359022912 + d * (503158650691349440 + d * (-433668410882936512 + d *
    (334029205058245568 + d * (-237193718551185600 + d * (160397534117253888 + d *
    (-105565086505475648 + d * (67544171979552896 + d * (-41696210716718208))))))))))) + d ^ 12
    * (24853387822352832 + d * (-14319414762422848 + d * (7920101511920768 + d *
    (-4170852890380928 + d * (2081467080627520 + d * (-978157580125760 + d * (428542545886272 +
    d * (-173884852976576 + d * (65301010016832 + d * (-22519828917632 + d * (6904497212288 + d
    * (-1770954943488))))))))))) + d ^ 12 * (347766462976 + d * (-44686922240 + d * (1996692480
    + d * (380258304 + d * (-53091328 + d * (-1346560 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt14 (d : ℚ) : ℚ :=
  238980103371589757709071506534204220889542722322432 + d *
    (-10782898891037663450173756675540059783794530099134464 + d *
    (-3358561219727488210862779030513557227923483379367936 + d *
    (51164239581026529500886893895309152420965705828007936 + d *
    (-97790150397827646760743227673550304524965519086845952 + d *
    (73304807536193039021001108661021012637133115486109696 + d *
    (192421604934061592682856093951819583629182691109240832 + d *
    (-729224924641862230685288083876683765822149918852120576 + d *
    (1171585094235536229746471132441023667262620534795403264 + d *
    (-810539088614747262170094525655130829424148005324062720 + d *
    (-1078469203218367409549766070160411597184836429987184640 + d *
    (4490913400320114101178184095529892275986228988096282624))))))))))) + d ^ 12 *
    (-7823540623983816609312082141390255699229707637159362560 + d *
    (7903918360117107490807751412941402215632342352576380928 + d *
    (-1355025783971844242599916535882540812668399622205472768 + d *
    (-13074370041224674683036542964466155271798312654134312960 + d *
    (32094744278619239597759156549084560944674422880098582528 + d *
    (-47087923699541555396432453619049199151481547027637075968 + d *
    (46399881089326254912543684853291299922831359525452775424 + d *
    (-20439235835112173343795315009325582398189872937468428288 + d *
    (-32300979116808896158297516276815925765625509691552956416 + d *
    (101124020004553840063788583093046800068245088246174580736 + d *
    (-163708129346256654830865060202062972944938103809880096768 + d *
    (192366789338045851513699327377974155157955438063872638976))))))))))) + d ^ 12 *
    (-164197441545529086066364212113972195155446668576750829568 + d *
    (71309647840546865265281941449993143578533709903953657856 + d *
    (73175103202564109774934385184823118522090856959230345216 + d *
    (-236369539672490078120199574214625976740215093096309850112 + d *
    (374281616047405553995167678719194472869859542649572163584 + d *
    (-445013882935935761047137530157716861996747681244788293632 + d *
    (421863482189109975809480976188374662437819737992609136640 + d *
    (-301781842811092297563029790408463915112303065521969430528 + d *
    (106453317903619352250812418100338037295484056296074248192 + d *
    (123995413155382692000858648317670527653553605544988114944 + d *
    (-342140964238567165415160127820143915365756386509576470528 + d *
    (505456545726869870864251073448522559888794277796215521280))))))))))) + d ^ 12 *
    (-585918349961822024346239586182181573991274297574572163072 + d *
    (574716908223839378099246710757898963745578326823388053504 + d *
    (-481601556702789575280402852728276835986958853060573528064 + d *
    (330005137697345264773859343649849787005608926222941159424 + d *
    (-150007888478770307019275277079572430886951947699032162304 + d *
    (-28700652635878028072465305825809923903869958134967042048 + d *
    (182228352265252526455750289440520808895842683973998215168 + d *
    (-295449769428880676188143989103589895521797902839646781440 + d *
    (362535627695376098730513550139331493603494649979276623872 + d *
    (-385602305572914573568775391936219199670090821955197861888 + d *
    (372291637217261507102063824198564226200438929563740012544 + d *
    (-333071578660389916744504920319955347877004916608653590528))))))))))) + d ^ 12 *
    (278855367434651525241880347517026277911711308231652933632 + d *
    (-219277265520553676116138740903128114024857314176103350272 + d *
    (161720917114756587829641673311882548229188477606029164544 + d *
    (-111019288943325069394495057404227716205556736117804105728 + d *
    (69647361097641362318249802564971785421461442188970033152 + d *
    (-38201802699214417526270266334260498022743381814615736320 + d *
    (15985187553188727882892488913436381385318710820225155072 + d *
    (-1562054717124377236995991059786843493994702207404212224 + d *
    (-6790080447094305442349597287462248805674846313391063040 + d *
    (10763477158169937087990396810805530859603431470894678016 + d *
    (-11831427983307714658445231910065226778947830326796484608 + d *
    (11163870331997082751455793206346203103397486358401122304))))))))))) + d ^ 12 *
    (-9616603980587552092193879701161276294418888022292430848 + d *
    (7764929283285258934464455234391327953951728949175779328 + d *
    (-5958286541598099252288489864912786013577057293211533312 + d *
    (4379498065529701637994152602077561572763394267841036288 + d *
    (-3098696347806823644906029125570780587087709771540987904 + d *
    (2117130766092769454240879453895779615364680295382777856 + d *
    (-1399591620952907426487640486219493672806489915817721856 + d *
    (896336126794462341435752710780900097929205347867164672 + d *
    (-556455154112010778139004022376214899973420354023718912 + d *
    (334917273618753716553749477944422245881710672412934144 + d *
    (-195365803930236637178897078286430542057678579193085952 + d *
    (110357572032222689028032625115823709971385114614562816))))))))))) + d ^ 12 *
    (-60280504505850720255751141510201412933190801057382400 + d *
    (31768998460583687254303895617752644827170419056312320 + d *
    (-16099175850083376810093565166188525967160112887365632 + d *
    (7803449412167793584130627299400892050971313885151232 + d *
    (-3587094753410100253077429683393903159655514739048448 + d *
    (1540612272887020305350521438484894343317799484784640 + d *
    (-600285052373818408421112861876177101018149765513216 + d *
    (197519814363294401339314051243150794767371791499264 + d *
    (-41587246220775302871611955250953109795054916468736 + d *
    (-8955091882762155847438770193941299089034841948160 + d *
    (18988942293988429140257098697962798314988673171456 + d *
    (-16114691220876883857529830666754850783581702193152))))))))))) + d ^ 12 *
    (10854541791914460385686453988610847553030207045632 + d *
    (-6496964026592376191603597269097717940873891414016 + d *
    (3598173576945603922718113832627695709074493276160 + d *
    (-1879255226251586602576406497560086994184770945024 + d *
    (935201166151556518025502935905857697635106553856 + d *
    (-446150649946391769949558374479063188804195844096 + d *
    (204803178299508524302021465967219813279656312832 + d *
    (-90671158648646844623132561450597749172488110080 + d *
    (38767240395489821848837116795108611658892181504 + d *
    (-16018238433720130051006573155764556473617874944 + d *
    (6397082627429062645618000991481891035213201408 + d *
    (-2468538237018831345502821115255202581221736448))))))))))) + d ^ 12 *
    (919796689325163738992642071657132053102592000 + d *
    (-330582303359636173792450642661563777769275392 + d *
    (114441099009944579205145729380429518658338816 + d *
    (-38089352146964964599327433301849790918164480 + d *
    (12160445535553716239288741281766027377770496 + d *
    (-3713513611755102935001703092928247510335488 + d *
    (1080882506046931300578115659327434020880384 + d *
    (-298556614466941757991794614866609362436096 + d *
    (77831933367888535060268964997558379479040 + d * (-19019359126870554515182400122887180124160
    + d * (4318693870382613929674796250631108034560 + d *
    (-900898174635630526092917673868159614976))))))))))) + d ^ 12 *
    (169983845082070267977985938725857656832 + d * (-28358027514856931213569449448674951168 + d
    * (4030897976900565142384516707217047552 + d * (-453943067332945035063473158197346304 + d *
    (32835344993336532344626834362597376 + d * (291348933301361872127489719926784 + d *
    (-481917162072994914677799140982784 + d * (67705432989823562019370868146176 + d *
    (-4020567043568710372965869158400 + d * (263607501097241580121395036160 + d *
    (-179055545283945249371762720768 + d * (57522839591964535932457058304))))))))))) + d ^ 12 *
    (-9437867522550791442815254528 + d * (703269471859735243568185344 + d *
    (37353445415614435614523392 + d * (-14783604604095082150232064 + d *
    (1364304638097868836306944 + d * (-9047111109688723243008 + d * (-6857765078321506549760 + d
    * (188510090344570552320 + d * (11868506940089565184 + d * (4740002026500653056 + d *
    (-315512135803731968 + d * (-55840225549090816))))))))))) + d ^ 12 * (1597295834431488 + d *
    (345033177563136 + d * (16128686686208 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt14 (d : ℚ) : ℚ :=
  41342195223363262076189349246457220169728 + d * (-1856348898497178302518970973016941270138880
    + d * (-1004085828472918185941910254523800878055424 + d *
    (9431960148480852593419066828164620689965056 + d *
    (-14959094399237855609506976089980840171528192 + d *
    (5079163644102663152028627885652051341278208 + d *
    (43841214242509566662488827434362287123104768 + d *
    (-122966754185609117834318750670363124488157696 + d *
    (156271850750045399936037821336885760836558808 + d *
    (-36121274945067782188904980379057196947743589 + d *
    (-299968995210623266587050691489194714795736442 + d *
    (762025046367405371737684744387279842624976631))))))))))) + d ^ 12 *
    (-1032538852965243164686190030871723105392350131 + d *
    (670263183982575350174368454459433073229445272 + d *
    (612739645461785958047796725048612074553089623 + d *
    (-2652387042989813198622916051969219124759087194 + d *
    (4668845080212291812952537448835858802437582462 + d *
    (-5414747999732817120681691700944471668149565902 + d *
    (3692915184200203100576210690290973359344228242 + d *
    (966554269248042080007669096114226894330558968 + d *
    (-7802459739809924963213826935464945413715410270 + d *
    (14773096419588615230136994562354721895956628329 + d *
    (-19099689682648876259928035680804371967272892630 + d *
    (18267052590279799050227224259671726664038688216))))))))))) + d ^ 12 *
    (-11081244611291236907128069627911217455152834359 + d *
    (-1662801833256405377834239096507071620277204792 + d *
    (17199091664788285662376095622732705424872987981 + d *
    (-31529853499333931375085817430376229678298638832 + d *
    (40628186218501395070468624829848875937009231521 + d *
    (-41661210055278302518610777416054928831467461089 + d *
    (33812868005184837831650019060121210480875253045 + d *
    (-18464237310831043237580472491540731283767525620 + d *
    (-1271644200186168930989816970553017543525256689 + d *
    (21448914968082728636541367863794563562655907683 + d *
    (-38300610623862528775877741473147535042400600398 + d *
    (49064077899917300547818804907230578261118815933))))))))))) + d ^ 12 *
    (-52434249544694524697148423865967266469811980998 + d *
    (48601434620761957668620406829895451974216910861 + d *
    (-38952774101124375884059127474289755756606612122 + d *
    (25585426863814489439843697825242446678771615475 + d *
    (-10787356020306838215133113571309908343158986030 + d *
    (-3394129495919774685814967048481342553486394573 + d *
    (15430418371991632021356641955589713568678781927 + d *
    (-24423867397440179609187713173792867122889718247 + d *
    (30080984641274121907015108227034512266519260131 + d *
    (-32593103465678158077386644135703069296848798273 + d *
    (32474269688218247109303024255358833616500672241 + d *
    (-30398016754586342608836178733020432595306430623))))))))))) + d ^ 12 *
    (27061076116878537680265132632957241959509739127 + d *
    (-23087611522193348149767201994364156061731506811 + d *
    (18975597712815659937915359565127744887510081184 + d *
    (-15079020333514946297596063225378410624202911263 + d *
    (11615741970547528680077738491960579399418931349 + d *
    (-8690384510669741350777228063875289709300168410 + d *
    (6323232540442423379209570946364238835044702009 + d *
    (-4478760977413762561040123092704786303046066274 + d *
    (3090023198759223193275758446486962936316549665 + d *
    (-2077292083489936677101480242217570565867667076 + d *
    (1360843704474039758204877011035367675484605209 + d *
    (-868643229113457222762666896064931849011811391))))))))))) + d ^ 12 *
    (540072087241420817469787505315959317389452536 + d *
    (-326885600197362420188821691648694541435781547 + d *
    (192450395324438581233854822782685064703294640 + d *
    (-110085265042087098210839469417524493304408009 + d *
    (61087966821262284288536162624686141342379360 + d *
    (-32815276791420705597628215729300371310919169 + d *
    (17013630668602657512074086137538711479827511 + d *
    (-8476992405261268769438704102177249522359971 + d *
    (4032289553809204272311369642257071860341665 + d *
    (-1811606425666386207607563445578791255616014 + d *
    (754018865757245292925626664410383627022409 + d *
    (-279174663443327851952687587537526768918148))))))))))) + d ^ 12 *
    (82162299207768867501225330511994839934196 + d * (-9780361936560903437140652278900539085699
    + d * (-11081888684840774003211468613463194698043 + d *
    (13180519655562700651046089970044274141360 + d * (-9998754376453854559042075186765297717530
    + d * (6398804321540368212972202677499598718241 + d *
    (-3711747020672294787660805793158804802188 + d * (2009584589270221298008017713799877541620 +
    d * (-1030526421429500658002337578224487105434 + d *
    (504679895504747873957009413723556558095 + d * (-237198547794522686837323448632105212565 + d
    * (107311029491813100265142029079812791037))))))))))) + d ^ 12 *
    (-46813886526374041346373949708187289422 + d * (19710297230143413152990613097677861902 + d *
    (-8011471537575551990469773065017461608 + d * (3142820510826589349905153703543607246 + d *
    (-1189052658473012989009384764284443890 + d * (433355203223018545151951435943811647 + d *
    (-151889417417092419099822277991366058 + d * (51086788553017021587132084692268656 + d *
    (-16443694869845847311344409151516289 + d * (5047980111990598942874926309114566 + d *
    (-1471584379298801128882798654356217 + d * (405098107860226906325955789123343))))))))))) + d
    ^ 12 * (-104522720411942068657013661386616 + d * (25029335960013510978648593235529 + d *
    (-5490664023251591289952066969832 + d * (1084628109518214248946415571906 + d *
    (-188505985506065168603801306732 + d * (27872680341296884877874995551 + d *
    (-3319647438617722790437940850 + d * (285429104701270373300868848 + d *
    (-12658912511508889511947659 + d * (-286742530711985309504203 + d * (-8610087844710288983899
    + d * (19015108829888597641655))))))))))) + d ^ 12 * (872972911636957947419 + d *
    (-1612766677735449506574 + d * (406324017989870662062 + d * (-52401105965573777153 + d *
    (3002537738912368392 + d * (125796536457129378 + d * (-31097134802832234 + d *
    (1217207455790956 + d * (14920457680200 + d * (10803728998311 + d * (-615770633367 + d *
    (-174731834039))))))))))) + d ^ 12 * (5032968259 + d * (1234219012 + d * (58451851 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_14 (d : ℚ) :
    orderSevenSelectionPolynomial d 14 = selectionExpandedAt14 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 14 =
      selectionNumeratorAt14 d := by
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
      selectionNumeratorAt14
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 14 =
      selectionDenominatorAt14 d := by
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
      selectionDenominatorAt14
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt14 selectionDenominatorAt14 selectionExpandedAt14
  ring

private theorem selection_cofactor_eval_at_14 (d : ℚ) :
    (selectionCofactor d).eval 14 = selectionCofactorAt14 d := by
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
    selectionCofactorAt14
  simp
  ring

private theorem selection_factor_at_14 (d : ℚ) :
    selectionExpandedAt14 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 14 *
        selectionCofactorAt14 d := by
  unfold selectionExpandedAt14 orderSevenDualKernelPolynomial selectionCofactorAt14
  ring

theorem selectionEvalAt14 (d : ℚ) :
    Internal.SelectionEvalCertificate d 14 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_14, selection_cofactor_eval_at_14,
    selection_factor_at_14]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 14 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt14 d
#print axioms solution
