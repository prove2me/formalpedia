-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:04:46.778042+00:00
-- url     : https://prove2.me/submissions/6dc611ff-d47d-4389-ad85-1efbc783616b

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval0.At1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 1

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt1 (d : ℚ) : ℚ :=
  -4096 + d * (-138240 + d * (-99072 + d * (20952768 + d * (-105745536 + d * (-930983040 + d *
    (17271193536 + d * (-140848115904 + d * (795974560704 + d * (-3504563879744 + d *
    (12685273668288 + d * (-38924776979712))))))))))) + d ^ 12 * (103282639242816 + d *
    (-240264119577792 + d * (494894267538048 + d * (-909110169560832 + d * (1496908974129792 + d
    * (-2216419720129152 + d * (2955913018777600 + d * (-3551190862952256 + d *
    (3838002458470272 + d * (-3720490347525504 + d * (3219921980639424 + d *
    (-2472055713072576))))))))))) + d ^ 12 * (1669899429322176 + d * (-983401876240704 + d *
    (501159207864768 + d * (-221629261694912 + d * (87669580618944 + d * (-33352398295872 + d *
    (13064038106304 + d * (-5068111603392 + d * (1727620116672 + d * (-486210176832 + d *
    (129317029824 + d * (-42638240832))))))))))) + d ^ 12 * (14673282240 + d * (-3527313216 + d
    * (500758848 + d * (-100318912 + d * (46550592 + d * (-10633920 + d * (326592 + d * (122496
    + d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt1 (d : ℚ) : ℚ :=
  -4800 + d * (-214720 + d * (1134208 + d * (21113472 + d * (-226359616 + d * (599863232 + d *
    (5747288064 + d * (-77144964352 + d * (513556244736 + d * (-2456553942464 + d *
    (9354543793408 + d * (-29727405088128))))))))))) + d ^ 12 * (80950482851392 + d *
    (-191996784098624 + d * (400892755250688 + d * (-742655542675456 + d * (1228905173174336 + d
    * (-1830270314601856 + d * (2477913272748928 + d * (-3089248602319616 + d *
    (3598824919429376 + d * (-3965119250910336 + d * (4149644295493376 + d *
    (-4103086329026816))))))))))) + d ^ 12 * (3790136144069056 + d * (-3233661958577856 + d *
    (2527493994317696 + d * (-1800483779241600 + d * (1164011924376640 + d * (-679708492258752 +
    d * (356460417240576 + d * (-166722511102720 + d * (68854783237440 + d * (-24705748082048 +
    d * (7504403164544 + d * (-1854245052416))))))))))) + d ^ 12 * (349303859200 + d *
    (-43773293056 + d * (2017019904 + d * (362180608 + d * (-54915072 + d * (-1359872 + d *
    (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt1 (d : ℚ) : ℚ :=
  6925582336 + d * (6990845706240 + d * (336564948303872 + d * (-6685008025616384 + d *
    (-318987857967710208 + d * (3844584607213944832 + d * (80523321412664164352 + d *
    (-1570427620804936073216 + d * (-1130013146883296067584 + d * (265174060375430720389120 + d
    * (-2697057726982110585552896 + d * (-1652949140862794172465152))))))))))) + d ^ 12 *
    (305001482137273120075022336 + d * (-3415868163917840139078074368 + d *
    (14476651324186840644635328512 + d * (91497954174558783543144611840 + d *
    (-2118700481175823116798944870400 + d * (19467920396565759620796203663360 + d *
    (-106436942891677813573282436218880 + d * (193412979782952670192421074108416 + d *
    (3170177768609246917304272605413376 + d * (-46722904236633149180196300031524864 + d *
    (406971878339807040578531742700011520 + d *
    (-2790250949577186276915275640818892800))))))))))) + d ^ 12 *
    (16311051992571615248307351735186227200 + d * (-84274931587458527404647106025466363904 + d *
    (392673542719136967755643209146059980800 + d * (-1671151552127343094354975528656422567936 +
    d * (6552801466111608500591085075596244156416 + d *
    (-23820645410334304992488930378413128810496 + d * (80637875840567291308976764474877519069184
    + d * (-255014281571101151761046903746600730099712 + d *
    (754981153493146555881506881823556512514048 + d *
    (-2094624705654588297265932711532365209141248 + d *
    (5445360152722979375899984242920927569117184 + d *
    (-13243733714485009270849301055400879074050048))))))))))) + d ^ 12 *
    (30021629519285204718683208548318284660342784 + d *
    (-62965970092089431398471599749514232155602944 + d *
    (120451665119193445922080661277320449164836864 + d *
    (-203902954248323412968281283999766710471360512 + d *
    (282555045530560953276514562945375827303333888 + d *
    (-230344093141993909141943401831355836408791040 + d *
    (-312464470919369044094419259693071013510381568 + d *
    (2214139652215327669358080189884440145645797376 + d *
    (-7353943383284867177116663712397555328978780160 + d *
    (19474016281020481326854362078577543595109646336 + d *
    (-45523028477908315212831571731748340946245517312 + d *
    (97626010055715640071995164250311985348682973184))))))))))) + d ^ 12 *
    (-195753782491474742928842093122349260962375925760 + d *
    (371024324004109501453948387705254419282235228160 + d *
    (-669326591497351038594607137585041139572164788224 + d *
    (1154614551887737438743899849578343224321603010560 + d *
    (-1910813138578780066573919188665142345832611184640 + d *
    (3040900107102170319808697934962309800144777248768 + d *
    (-4661528812717172786227112031358848413708460752896 + d *
    (6891728532930394403954245874170097385225546891264 + d *
    (-9834944110019856320693647447018277204816683335680 + d *
    (13555047580095276117126996056594520699361732591616 + d *
    (-18048876473074690575197919408050355497601178796032 + d *
    (23219973682703073922075502501622978009765493080064))))))))))) + d ^ 12 *
    (-28859914226845797294862208355675580133663138906112 + d *
    (34644160478136980874263779803871847957085867737088 + d *
    (-40148144965761976789854516762831645484607245123584 + d *
    (44885989348767970726604024882531126368984276140032 + d *
    (-48369316315709401187765494344537220545271814422528 + d *
    (50178075939234057258441253391357694906394746290176 + d *
    (-50030746347752710701343064126540906271707054735360 + d *
    (47839259287715698873040872432943448080145310810112 + d *
    (-43735583813086955032239169768377966965059457908736 + d *
    (38062122568745999999166608608198257374953409347584 + d *
    (-31325836723205069848437528380037048544051287293952 + d *
    (24124317200585236182921333221287340641112588288000))))))))))) + d ^ 12 *
    (-17058544081756932859869368005352641741715802423296 + d *
    (10649931532401891146184673990292133709611067244544 + d *
    (-5277620165245052561590926082701173783472473899008 + d *
    (1146399433521167237270901639858394673076098301952 + d *
    (1712139987136352309508382468609736222267368800256 + d *
    (-3410281374242610360369019798680174926954879254528 + d *
    (4157166058414645162568144147016183081254492045312 + d *
    (-4206558132119468523978695456774089441518695481344 + d *
    (3810427754961690807517779736319589873151650824192 + d *
    (-3185576215179067560010455365427025762391579688960 + d *
    (2495880707192846761488781302366274092386135572480 + d *
    (-1848707044325820075550712650034021615482632667136))))))))))) + d ^ 12 *
    (1301521304696394204444955387575764652895465111552 + d *
    (-873933081682956797950483578643747839341152174080 + d *
    (560975420252929308243356214402237125810087264256 + d *
    (-344750706074759146165329677159816821791478775808 + d *
    (203039208409929777165923241723805351257790742528 + d *
    (-114658444639495537867434542187911994822559531008 + d *
    (62098098059836780196344707682040732478239145984 + d *
    (-32253036700036714150034604334115413759555272704 + d *
    (16060143148435848532124448604372917483182489600 + d *
    (-7662676940938892327386478248502951885556416512 + d *
    (3500509212846561636387157012861876303434088448 + d *
    (-1529566992919325701722957137162332613737447424))))))))))) + d ^ 12 *
    (638489261247261536336504588186389770059644928 + d *
    (-254233696934961022414689865161593369212223488 + d *
    (96388725677244244518222586178039578048331776 + d *
    (-34722216465416906646461735032669280621297664 + d *
    (11854505230033481184491413108097947167883264 + d *
    (-3824392194211217371246419137460149983641600 + d *
    (1161748796656271289216604260415766843621376 + d *
    (-330903614705789265274797243744252102967296 + d *
    (87925349429782862077326447095804910370816 + d * (-21658024028749708885002953472506386186240
    + d * (4906389225071270631232874368203491901440 + d *
    (-1011620665639213894859079553806566948864))))))))))) + d ^ 12 *
    (187134960874131478245349584325416058880 + d * (-30407054833769967650265289388633882624 + d
    * (4191775960441889751912652046421458944 + d * (-458204582696320766426763214131822592 + d *
    (32979640320420742940330070976233472 + d * (-114778978350263812169428865384448 + d *
    (-343777642103511713609731137601536 + d * (44566702085377596652572829024256 + d *
    (-2375459742288283450450750734336 + d * (434862223419633307800318246912 + d *
    (-239067627868701451237572739072 + d * (64194708490262024170036527104))))))))))) + d ^ 12 *
    (-9581619601621354131600441344 + d * (656721565829395545752076288 + d *
    (41435874753434574935031808 + d * (-14677760485379230013849600 + d *
    (1356087461596355574366208 + d * (-12553615881295539994624 + d * (-6808639614977061945344 +
    d * (233509237057657503744 + d * (12140538513444569088 + d * (4489968141311934464 + d *
    (-331342754651045888 + d * (-56439337134850048))))))))))) + d ^ 12 * (1580153979273216 + d *
    (344846971437056 + d * (16128618528768 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt1 (d : ℚ) : ℚ :=
  911 + d * (922255 + d * (46969881 + d * (-747214531 + d * (-44428744588 + d * (380163239273 +
    d * (11971078677805 + d * (-173941224227042 + d * (-729646717310248 + d * (33837741181250652
    + d * (-251659131120781680 + d * (-1164316729461944821))))))))))) + d ^ 12 *
    (38337377345172242640 + d * (-330263098248622463966 + d * (695594991285748083433 + d *
    (16192056000965275163546 + d * (-235881593635798054655052 + d * (1766547992605466779355090 +
    d * (-7312890519570188810340707 + d * (-7234497515972180325438663 + d *
    (440958320203907997258436257 + d * (-4788820752089758205734589381 + d *
    (36559640845692109573922112875 + d * (-229021648408155449524208113640))))))))))) + d ^ 12 *
    (1245080792612627933596584873778 + d * (-6043452786059702948468935235370 + d *
    (26642276671625673731438199282457 + d * (-107908016396826137243854571535409 + d *
    (404900615332623360657316863383597 + d * (-1416490440446689361310496398271183 + d *
    (4643426191672185865707701569968850 + d * (-14322421209880291609463446103996449 + d *
    (41711417426868992482938260562230641 + d * (-115040206678280452012372968803020027 + d *
    (301255635180211261224903718736160596 + d *
    (-750795127410657443088029441845704784))))))))))) + d ^ 12 *
    (1784512902949953686141424316570427166 + d * (-4052854825617414768843665289903507880 + d *
    (8810679017430317760702121556916489813 + d * (-18364099243282157258451201420285466390 + d *
    (36752974554225038639726268451106563133 + d * (-70725523483502016892118311657096544191 + d *
    (131028542960968720612240848110411909051 + d * (-233965612724133964962729680566780247977 + d
    * (403057594026992103258962015627205940294 + d * (-670475701890834689650741419428432502369 +
    d * (1077726495193111474936612799712479594761 + d *
    (-1674894896605519960597446052648111232753))))))))))) + d ^ 12 *
    (2517668592676590816942470992252473955022 + d * (-3661467701125884164079529941369457749185 +
    d * (5152376375979898657807252480605875766391 + d *
    (-7015262723592857051064443837819164030998 + d * (9240431763882521519545529503766456841541 +
    d * (-11771204130131393251061072331779165466049 + d *
    (14495640252028968585188277161317755689220 + d * (-17245853620820585958139401220091759036596
    + d * (19807647021363913924805567397110089494366 + d *
    (-21941442347464080931511575550587603195019 + d * (23412878894261330837878938088594463328438
    + d * (-24028617390744256258489701276607437140975))))))))))) + d ^ 12 *
    (23670645347931139140159303867409952647933 + d * (-22321560366999152631761805178365775766846
    + d * (20074418023873925034504479948960741092121 + d *
    (-17123718416664693663446202777845876598531 + d * (13738303895995145849196765727012618278541
    + d * (-10221229890560502610297529837344669500328 + d *
    (6864815217706377162668605511250353277717 + d * (-3910130463114908085090820100395921462087 +
    d * (1518816109423224468697169135137451228920 + d * (238236636906305547265385494037970309729
    + d * (-1375110588684987933437804454947128133075 + d *
    (1971699553817831890607015885490048939457))))))))))) + d ^ 12 *
    (-2147342391210027635211224154121497723470 + d * (2033937648146972595487920732811735506560 +
    d * (-1753922112690499688520205705364545393177 + d *
    (1406116950830096409793458466554576230867 + d * (-1059899073479495987878650776877682935308 +
    d * (756194822787361067811625467305731303253 + d * (-512792175532503349579057293819387430000
    + d * (331401224171758206352343723409695810186 + d *
    (-204465476710160139239181537179759768265 + d * (120557866513546600770981348204217073947 + d
    * (-67970347302220785582086805103583756411 + d *
    (36648517428931524504840827297801343396))))))))))) + d ^ 12 *
    (-18893934107256314344094647864188708312 + d * (9308905488542001959632608116246386387 + d *
    (-4379621059368839066556394309417547334 + d * (1965424730188873229081234819592274427 + d *
    (-840117603026121056987545090362705248 + d * (341442736858889039341919362009356265 + d *
    (-131658647832411883678200664552476568 + d * (48039326902605836273534094109769469 + d *
    (-16534456351512774867167412962210812 + d * (5347834054606639367587798053383706 + d *
    (-1617958925836169908772285961526763 + d * (455340460995813800363230203321230))))))))))) + d
    ^ 12 * (-118388926073822143003195282668563 + d * (28196002446769012377330928898766 + d *
    (-6084803631665426784424683022146 + d * (1172960199709884625131975507845 + d *
    (-198047923520244686599124889676 + d * (28461646285853330611075089904 + d *
    (-3327155970887966203324319842 + d * (292397130453342587312744164 + d *
    (-16785765449618806277681759 + d * (705412867889736180431064 + d *
    (-139777791590329596189000 + d * (25984501885618906626813))))))))))) + d ^ 12 *
    (1652083258554191139748 + d * (-1791787303214507995440 + d * (417292953154700574800 + d *
    (-52058437588815129369 + d * (2970770782084712719 + d * (119099477494608347 + d *
    (-31131491713436887 + d * (1335537819085190 + d * (16238407018451 + d * (10021239255809 + d
    * (-668034901267 + d * (-176697278065))))))))))) + d ^ 12 * (4975157545 + d * (1233558612 +
    d * (58451500 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_1 (d : ℚ) :
    orderSevenSelectionPolynomial d 1 = selectionExpandedAt1 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 1 =
      selectionNumeratorAt1 d := by
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
      selectionNumeratorAt1
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 1 =
      selectionDenominatorAt1 d := by
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
      selectionDenominatorAt1
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt1 selectionDenominatorAt1 selectionExpandedAt1
  ring

private theorem selection_cofactor_eval_at_1 (d : ℚ) :
    (selectionCofactor d).eval 1 = selectionCofactorAt1 d := by
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
    selectionCofactorAt1
  simp
  ring

private theorem selection_factor_at_1 (d : ℚ) :
    selectionExpandedAt1 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 1 *
        selectionCofactorAt1 d := by
  unfold selectionExpandedAt1 orderSevenDualKernelPolynomial selectionCofactorAt1
  ring

theorem selectionEvalAt1 (d : ℚ) :
    Internal.SelectionEvalCertificate d 1 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_1, selection_cofactor_eval_at_1,
    selection_factor_at_1]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 1 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt1 d
#print axioms solution
