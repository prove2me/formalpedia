-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_11
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:36:07.671979+00:00
-- url     : https://prove2.me/submissions/ffd43170-c18a-4075-83bb-abcc5db4a604

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval2.At11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 11

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt11 (d : ℚ) : ℚ :=
  -5931313667012096 + d * (-2526319682937600 + d * (8922450599407488 + d * (-19261663269173312 +
    d * (23051187753314304 + d * (-1464229389509760 + d * (-44690872288017984 + d *
    (93605060339512896 + d * (-121418605760429376 + d * (104981717912794816 + d *
    (-31799056927198272 + d * (-83516297513121792))))))))))) + d ^ 12 * (212030976462349376 + d
    * (-326187293237161152 + d * (403506088638588288 + d * (-431426131413268992 + d *
    (412230680642504832 + d * (-358512415106593152 + d * (286152418698574720 + d *
    (-210632389710309696 + d * (143705641440133632 + d * (-91054752459725184 + d *
    (53369770172228544 + d * (-28790143959247296))))))))))) + d ^ 12 * (14294970883813056 + d *
    (-6541198342138944 + d * (2730741978339648 + d * (-1018419129321152 + d * (339464939010624 +
    d * (-108882320745792 + d * (37569171470784 + d * (-13296518549952 + d * (3990344893632 + d
    * (-914829874752 + d * (199811893824 + d * (-66298869312))))))))))) + d ^ 12 * (22586456640
    + d * (-4614179136 + d * (436085568 + d * (-78822592 + d * (47979072 + d * (-10610880 + d *
    (326592 + d * (122496 + d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt11 (d : ℚ) : ℚ :=
  -7028570477332800 + d * (-3306617653078080 + d * (13451647767354368 + d * (-32076543406795008
    + d * (48199904197564224 + d * (-35312723837684288 + d * (-14269429135945856 + d *
    (79133712267461248 + d * (-140690803594966144 + d * (177867707653103296 + d *
    (-164148234216602752 + d * (98781485671560192))))))))))) + d ^ 12 * (-1147642787811648 + d *
    (-105569824310744384 + d * (194372371386412928 + d * (-243221957154354816 + d *
    (248693907818714176 + d * (-222369236664854656 + d * (179976128853976448 + d *
    (-135384532774400256 + d * (97145563548865536 + d * (-67608981917042816 + d *
    (45711774883498496 + d * (-29890920379585536))))))))))) + d ^ 12 * (18846953003363136 + d *
    (-11418144493650496 + d * (6607443541227776 + d * (-3630670379363840 + d * (1883329682691520
    + d * (-914936243886272 + d * (412743136419456 + d * (-172043068426880 + d * (66022889697600
    + d * (-23014421341568 + d * (7044627062144 + d * (-1790416874496))))))))))) + d ^ 12 *
    (348082201600 + d * (-44476606976 + d * (2001383424 + d * (376086528 + d * (-53512192 + d *
    (-1349632 + d * (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt11 (d : ℚ) : ℚ :=
  42793819462476988436154226764449602681613582336 + d *
    (-1883999312261083047882734135242186618440054210560 + d *
    (-1892567287586205907353247994738982254339621388288 + d *
    (14849251020747021255777383639091862557422836514816 + d *
    (-25414029682416828101853730099212007959052895387648 + d *
    (-3327207174984326548124389896238705281636750327808 + d *
    (140900463117967124780704174824511791920692915863552 + d *
    (-380002103356993602065959341662830012257099900256256 + d *
    (466170221870553708306425391914790110218988116770816 + d *
    (138156242435167662197793111309501751279378767544320 + d *
    (-1960666813173143727286350071848941023081530999177216 + d *
    (4715867815906467592900277953278631506606364653518848))))))))))) + d ^ 12 *
    (-6267147041730695788461957988373793373955197518741504 + d *
    (2418973082115155882532936271429363694613715254771712 + d *
    (11293144126125942992952024575668061572029162244800512 + d *
    (-35424351039019210360016974999896720373781167913041920 + d *
    (61329874035604070064225317086936292810724300795412480 + d *
    (-68341831602362862037916787630872967520961581682524160 + d *
    (27958250845839076966196546845292489653924465727242240 + d *
    (82539965465104353605731981020754572613690878135894016 + d *
    (-259578085728263233273995393975314375556090696603009024 + d *
    (454581414078869859697776189234208009133212539648475136 + d *
    (-569855605378899338716859944179975457262477497515376640 + d *
    (479751973619696325678170166685028194691743325160734720))))))))))) + d ^ 12 *
    (-78413390742417643288301309501862735227298925065011200 + d *
    (-658253212652708061468117623720584992336917143760666624 + d *
    (1620760002469771256448587330899026618684456880534978560 + d *
    (-2552263803079500979652005977725361698237646071637999616 + d *
    (3091377116719388808476655961967056850196196106027401216 + d *
    (-2869826988998730065560779295866208721286225736263008256 + d *
    (1639724566909832443385745615235464059634222611004391424 + d *
    (611459573899202017432720787136458672882019598825422848 + d *
    (-3601755341709029365785411335691213130634626393594396672 + d *
    (6779331261394373453993756682644085015141108324141105152 + d *
    (-9431468613495901843656825518443808432325810874859913216 + d *
    (10849787976929828825129171799571775897395234187472535552))))))))))) + d ^ 12 *
    (-10504592702864233838875158095260565808152051841555234816 + d *
    (8178511010855802452225356308970585444434569619346292736 + d *
    (-4023451844799281689804473598688003961409731574128705536 + d *
    (-1470847372500372221383461064357913173920069456199155712 + d *
    (7582872403389609602408983731823963040012187512183717888 + d *
    (-13507692422773341478938438921504926073063168205763379200 + d *
    (18508556256992505874841433993758100482242397027943841792 + d *
    (-22037599938680399548192227311874652603115019555839934464 + d *
    (23804537249079171517098244833563318680081441416326676480 + d *
    (-23787949932233356249962281825305716558353735461507170304 + d *
    (22197483367746000979381455390264762683770217048911904768 + d *
    (-19403893511497535382916182190179620128486942871779803136))))))))))) + d ^ 12 *
    (15856647997973785571784791782569460959043739336175779840 + d *
    (-12006574698549838283221661266025297387405095324525527040 + d *
    (8245746573935275893450749194521386528337656228135305216 + d *
    (-4870431921207570637459024210905293880022423945681305600 + d *
    (2067186578808150789783649917244678700606902454997483520 + d *
    (81956891322975903425850124059983022979648883020791808 + d *
    (-1581383470022591399063505798982148425362242519583686656 + d *
    (2497386113545071442127120689072384689207123697049534464 + d *
    (-2932803409021415224684583598691378409600636414687969280 + d *
    (3004716356277495575218706405260820126892909667581689856 + d *
    (-2827348805262295471295157080043469654067041492825014272 + d *
    (2500800448412457289367467482542410738655992922814808064))))))))))) + d ^ 12 *
    (-2105163100785333122355861337313819493680173586720489472 + d *
    (1698955644554010111967562365632319407319273473728053248 + d *
    (-1320586312051507175589663839834069554767657035158257664 + d *
    (991598294045178407004750202535559462358388547183706112 + d *
    (-720662213667497261011564483767314301129488436072808448 + d *
    (507554750320259042724004513314461728096637276564750336 + d *
    (-346641812329563502927645078358410671779860901201182720 + d *
    (229627104668181507452452451204009532962360888360435712 + d *
    (-147512574224002543092086536461050278525170608849289216 + d *
    (91840873939833571843559079366032197916085326821720064 + d *
    (-55356958239736922623609970840322365877414347617861632 + d *
    (32247751809728837552521930635644315447515976490024960))))))))))) + d ^ 12 *
    (-18109579414642769361584923090994694172736869170937856 + d *
    (9766279847492714255861751703018794432466027611684864 + d *
    (-5027756056415011142249371681237790960626570971578368 + d *
    (2446858608959876724036171124951387274066733188513792 + d *
    (-1106308159076458082811361536012881017543432688369664 + d *
    (448417234338826364194007619785986859206675295895552 + d *
    (-148366789245984611183529677186786147888626278596608 + d *
    (25401988260216546613058271124762030616780102434816 + d *
    (16122491568874173679245526807028823330004465876992 + d *
    (-23934074727680789911597170568246590372306312232960 + d *
    (20157602799553901365812705100537253163949964656640 + d *
    (-14035959140037819316487611859630934871569767858176))))))))))) + d ^ 12 *
    (8794987474632495838346955441729398535194129989632 + d *
    (-5126079240597986935876959125547435186912101662720 + d *
    (2824540349028019401637476001100321643636202930176 + d *
    (-1484750537127825688679015947960358701757500489728 + d *
    (748614411515648715282961433503250761901250183168 + d *
    (-363266427753165763331212853988941573857161248768 + d *
    (170005971679273899213367174271619616632207048704 + d *
    (-76826775864003849730428484237894758260101873664 + d *
    (33545961564456826869279397918720610538479943680 + d *
    (-14154989611100355628552449482869846594403172352 + d *
    (5770468082190347696099583865042026197951971328 + d *
    (-2271341074921794885579530156764962591940542464))))))))))) + d ^ 12 *
    (862415353523474251786624478261775293391044608 + d *
    (-315472636323659204201225982372977457525424128 + d *
    (110997631708892886278522800828631687355170816 + d *
    (-37488569321515356331237092184036049226563584 + d *
    (12124016711860045908778757397573271404150784 + d *
    (-3743253417157429169124468036075729321984000 + d *
    (1099282790662702962079691711155329772814336 + d *
    (-305682457401252450237157303396618758782976 + d *
    (80043342357099619294176406348232435695616 + d * (-19601296571720892863689142717557141667840
    + d * (4450152708293795913287612537973833728000 + d *
    (-926166543840151643527176623634371313664))))))))))) + d ^ 12 *
    (174000636929560882899469213347229204480 + d * (-28854582444165836099996312006450479104 + d
    * (4071958701058699009504727667778781184 + d * (-455154295778097805486775433255452672 + d *
    (32813897385200783968889882974093312 + d * (214470032822010257505213386063872 + d *
    (-452128130276750281616197206409216 + d * (62432679107889882226450821021696 + d *
    (-3622526206204977560720847405056 + d * (300495536333628889807304261632 + d *
    (-192868714947484767059621445632 + d * (59078653111564888610889007104))))))))))) + d ^ 12 *
    (-9470821802652005779978584064 + d * (692321034015298014010933248 + d *
    (38287461491644028150611968 + d * (-14756631442984489597009920 + d *
    (1362514815628209146298368 + d * (-9869277437755098660864 + d * (-6847638798734527299584 + d
    * (198842470509003669504 + d * (11929768312856117248 + d * (4682282635340283904 + d *
    (-319165392169730048 + d * (-55978482068881408))))))))))) + d ^ 12 * (1593340021702656 + d *
    (344990206918656 + d * (16128670957568 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt11 (d : ℚ) : ℚ :=
  14721387509167722524743644488153313221 + d * (-644000751247259440675013551417294953205 + d *
    (-838745275942966029554142854788253882019 + d * (5226738124359993698175784185288179964029 +
    d * (-7051463300429531895769551426201694202208 + d *
    (-6275554229626523450345854991152127963037 + d * (52507370867208026086375113265328249122475
    + d * (-114624956106230139104924123694586503916732 + d *
    (95192791646038996154941955160647273086812 + d * (158158139579790741042058065288946988227942
    + d * (-718268833162681138262460452555712044961910 + d *
    (1340085300173793331823101917863662240365929))))))))))) + d ^ 12 *
    (-1270211529715795840689737532844188525648960 + d *
    (-566887037881759826848369876148321438765086 + d *
    (4816682594200239408293159357921423557722963 + d *
    (-10569218667438140999197688840301466010193634 + d *
    (14476355049224422129728941216058271242310478 + d *
    (-11060227026564188200368366655396887782279120 + d *
    (-5076505160518446810255459718722504247457047 + d *
    (35429710925384708466597207180211573410384417 + d *
    (-73678805341231402706256229279506911047776993 + d *
    (104018829492529842310254997814527388382525879 + d *
    (-103917300311712264026785186265033736643751065 + d *
    (51882124269836646048736800089662926132595370))))))))))) + d ^ 12 *
    (61697075255871135124198703081587018946172428 + d *
    (-224754370585851165543045610468264436442866520 + d *
    (399617146653536018959740305219129366496184507 + d *
    (-528325683172011539880465825837443018048097179 + d *
    (547253526173942629587580841950686216811611267 + d *
    (-407201896758580432173883161898583483927008373 + d *
    (92481957256327847288329267281368693117991610 + d *
    (367769729774589499429158659416564737833047341 + d *
    (-900482486120184662327904178625828342522950239 + d *
    (1402158788219501225263670183723733133197294543 + d *
    (-1761283002288325645420067680378870852517861624 + d *
    (1883256605276484098134054104463991518553033236))))))))))) + d ^ 12 *
    (-1711084671582808593297368647144628758727219914 + d *
    (1236782894556292966764821708251258627844428020 + d *
    (-501517424583577864967911236448738762452841267 + d *
    (-414343685067162106441165308891769061191166920 + d *
    (1407785750310303590714511627502699884218993353 + d *
    (-2371865627446110072099819816706885598452635251 + d *
    (3212486410587850194919805976092845759125905741 + d *
    (-3860360656027583008965611018983426983658920657 + d *
    (4276892460906426597024013992928337955606688824 + d *
    (-4454189168681412009352776060345397793007836349 + d *
    (4410476289748919884595243876606421348441919591 + d *
    (-4182722513482521670919924584032310837014841703))))))))))) + d ^ 12 *
    (3818321501454612344699094967837799824833385722 + d *
    (-3367354727839571114729281731293753525501716115 + d *
    (2876444328897608288450306766959915159523247411 + d *
    (-2384655587735800610448993440837944718300207258 + d *
    (1921443409944930970479407444733261742059390211 + d *
    (-1506320029725208743665359604288847959670753499 + d *
    (1149763751442600787365692457033315148648279840 + d *
    (-854864171661925787926687074762066900538924046 + d *
    (619263708300488137676965643749701685613650896 + d *
    (-437063777729706672406027366264867879261007339 + d *
    (300481827220022468419925978944960475181301888 + d *
    (-201150786091716714271875332257833164379862085))))))))))) + d ^ 12 *
    (131034796602960532804319903115273189449520783 + d *
    (-82991582883570921804678545275010509311644376 + d *
    (51044343359329644817306242999154918740000131 + d *
    (-30438848860004778567984288787594224936830581 + d *
    (17559785840475921490141623796906787079414551 + d *
    (-9769680333514471430131238261302483420614158 + d *
    (5218731499587325182963664899922325086929837 + d *
    (-2658265915864231575244504007667251816112377 + d *
    (1276739644205286746949929020739956305234510 + d *
    (-566517848681374786887908413306857079634681 + d *
    (222345636033029883654323445142236340706005 + d *
    (-68141303876850201975978491194081263872853))))))))))) + d ^ 12 *
    (6816022217108547314216956175788463598240 + d * (12508356652197905532479054628157414417550 +
    d * (-14927867994494306609930842141324299010837 + d *
    (11891795089053937876704319104777630399767 + d * (-8058655045628102991726036349943179419768
    + d * (4962813356449951568516703721757790694183 + d *
    (-2855019574112554819621619443674637814830 + d * (1555886815300343049835937023261698891166 +
    d * (-809600094069005072403751369763211601945 + d * (404156891216818179014807490097130645917
    + d * (-194124397877979740629849901709424086091 + d *
    (89869868181424940417388739182896397706))))))))))) + d ^ 12 *
    (-40137569104485940359027553866972391622 + d * (17299175040308719687847513946515317967 + d *
    (-7193795431450947863051871338542546654 + d * (2884586747912447982916407108719585697 + d *
    (-1114189305723990280720821394797543318 + d * (413961649192898382291427450670096505 + d *
    (-147662144843570135302336534783106688 + d * (50449143331058484452236624745946509 + d *
    (-16460062642143850544763212567347672 + d * (5109839288946640658150682816277716 + d *
    (-1502354369810612459633841952261903 + d * (415872884250713037957553151044270))))))))))) + d
    ^ 12 * (-107563854523665921732574882391913 + d * (25741098127211805482133024933016 + d *
    (-5627822281613337545461424497406 + d * (1105650392218088945547084247745 + d *
    (-190869650544799242089513275676 + d * (28029759558437931645474588514 + d *
    (-3322165649415011693138861682 + d * (286766506759594525735197854 + d *
    (-13552907328730935600274539 + d * (-62289960147214897940446 + d * (-39002484932978644245130
    + d * (20665748712334337240333))))))))))) + d ^ 12 * (1053062416465640134358 + d *
    (-1654450109726233904760 + d * (408831038049326890980 + d * (-52316538521700575699 + d *
    (2995516216954115919 + d * (124216919990255877 + d * (-31108615323829947 + d *
    (1244358222127600 + d * (15219948438471 + d * (10623092248719 + d * (-627831752757 + d *
    (-175185398045))))))))))) + d ^ 12 * (5019627325 + d * (1234066612 + d * (58451770 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_11 (d : ℚ) :
    orderSevenSelectionPolynomial d 11 = selectionExpandedAt11 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 11 =
      selectionNumeratorAt11 d := by
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
      selectionNumeratorAt11
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 11 =
      selectionDenominatorAt11 d := by
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
      selectionDenominatorAt11
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt11 selectionDenominatorAt11 selectionExpandedAt11
  ring

private theorem selection_cofactor_eval_at_11 (d : ℚ) :
    (selectionCofactor d).eval 11 = selectionCofactorAt11 d := by
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
    selectionCofactorAt11
  simp
  ring

private theorem selection_factor_at_11 (d : ℚ) :
    selectionExpandedAt11 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 11 *
        selectionCofactorAt11 d := by
  unfold selectionExpandedAt11 orderSevenDualKernelPolynomial selectionCofactorAt11
  ring

theorem selectionEvalAt11 (d : ℚ) :
    Internal.SelectionEvalCertificate d 11 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_11, selection_cofactor_eval_at_11,
    selection_factor_at_11]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 11 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt11 d
#print axioms solution
