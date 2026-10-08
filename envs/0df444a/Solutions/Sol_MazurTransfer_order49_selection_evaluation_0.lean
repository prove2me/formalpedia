-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:57:36.728047+00:00
-- url     : https://prove2.me/submissions/c3bf6a05-6223-4eb8-ab62-62eae1f84efa

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval0.At0. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 0

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt0 (d : ℚ) : ℚ :=
  0 + d * (0 + d * (0 + d * (-64 + d * (8064 + d * (-416256 + d * (11645760 + d * (-201910656 +
    d * (2411073024 + d * (-21239588288 + d * (144502377792 + d * (-784029483072))))))))))) + d
    ^ 12 * (3473855356864 + d * (-12800864241984 + d * (39798488027904 + d * (-105587611838016 +
    d * (241130730158976 + d * (-477030598322496 + d * (820999262298496 + d * (-1232110667497344
    + d * (1613156304571968 + d * (-1840154157294528 + d * (1823241234612480 + d *
    (-1561580059780608))))))))))) + d ^ 12 * (1149000214432320 + d * (-721546111788480 + d *
    (385274214915456 + d * (-176223033281216 + d * (71564111368704 + d * (-27881598102336 + d *
    (11172059428032 + d * (-4425556498176 + d * (1541549539968 + d * (-445122736896 + d *
    (121124554368 + d * (-40142777856))))))))))) + d ^ 12 * (13898463744 + d * (-3418259136 + d
    * (507226176 + d * (-102468544 + d * (46407744 + d * (-10636224 + d * (326592 + d * (122496
    + d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt0 (d : ℚ) : ℚ :=
  0 + d * (0 + d * (0 + d * (0 + d * (6144 + d * (-355328 + d * (9750528 + d * (-169938944 + d *
    (2066597376 + d * (-18368803328 + d * (125163169664 + d * (-679350851008))))))))))) + d ^ 12
    * (3017630620800 + d * (-11166484410496 + d * (34821297423104 + d * (-92255538409408 + d *
    (209223633234368 + d * (-409984240190528 + d * (703618332094528 + d * (-1077640884266304 + d
    * (1505393955688448 + d * (-1952891751625152 + d * (2367360335156864 + d *
    (-2663106206604928))))))))))) + d ^ 12 * (2743255939917760 + d * (-2557772199344832 + d *
    (2144657798743168 + d * (-1613044130619008 + d * (1086695719330240 + d * (-654215541123136 +
    d * (350572824517824 + d * (-166261655241024 + d * (69173042427456 + d * (-24878509386112 +
    d * (7549761181568 + d * (-1860539453440))))))))))) + d ^ 12 * (349440341504 + d *
    (-43702770176 + d * (2018583552 + d * (360790016 + d * (-55055360 + d * (-1360896 + d *
    (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt0 (d : ℚ) : ℚ :=
  0 + d * (0 + d * (0 + d * (0 + d * (0 + d * (0 + d * (0 + d * (0 + d * (0 + d * (262144 + d *
    (103546880 + d * (-33421787136))))))))))) + d ^ 12 * (4061744594944 + d * (-306157964754944
    + d * (16825387463475200 + d * (-726409007042658304 + d * (25583291192503959552 + d *
    (-750700126416607903744 + d * (18617205603740507176960 + d * (-394738735386056043790336 + d
    * (7229153105580738231664640 + d * (-115422767184608763114160128 + d *
    (1620417012808174929184292864 + d * (-20159352433846671482572767232))))))))))) + d ^ 12 *
    (223825287229867581404102262784 + d * (-2231934172640756910311492288512 + d *
    (20102186662669140531831980687360 + d * (-164341185333650934058735069822976 + d *
    (1224773581635786041269873161535488 + d * (-8351493477981272294095408031596544 + d *
    (52264219359380383325952765886726144 + d * (-300924953088455450468836082143199232 + d *
    (1597180889306899471289542866849234944 + d * (-7824427748962461509260647410655297536 + d *
    (35400277541078052746361837566171283456 + d *
    (-147871377301024543761129154481529815040))))))))))) + d ^ 12 *
    (569403717591548582542497579762213191680 + d * (-2014358964782669804629158181198498103296 +
    d * (6503895429748633914184975294168545361920 + d *
    (-18924468515749212738830303458359837720576 + d * (48334410207905885797223543337892434673664
    + d * (-101526585396549520499830318209358024409088 + d *
    (137379738908185654802129950378163644661760 + d *
    (123175509460437323258327431343467098800128 + d *
    (-1835610487284834033126769693302245087772672 + d *
    (8904592326169094329116375829929760519618560 + d *
    (-32938065692700355987192180357120134828261376 + d *
    (105263091292683578368964596750183387535245312))))))))))) + d ^ 12 *
    (-303900544909154501070143754138116476151791616 + d *
    (809914874257496385855343814367655651576643584 + d *
    (-2017220075217139272894588598084427458652143616 + d *
    (4732162283256625172759827290052961515408719872 + d *
    (-10510936806332862518550877598838508546284584960 + d *
    (22186839228479315726778481029514789854351720448 + d *
    (-44622825221409267535467339502633984154631143424 + d *
    (85670936594746329001862511744861220717930479616 + d *
    (-157213302539387521816682266197621883772636758016 + d *
    (275997062641954526924995914083810554551211917312 + d *
    (-463783884190698461162039247124569115167979995136 + d *
    (746181922374352200741030795200473929226090971136))))))))))) + d ^ 12 *
    (-1149522760061316349066145312181918779343173058560 + d *
    (1695408773921607064281886312756448718710692118528 + d *
    (-2393161369145920452971417290553214021153627045888 + d *
    (3231300417530709196650032144727769120400590241792 + d *
    (-4170158295249399047352115792800232232731314749440 + d *
    (5138394379000984155522706677000158959999859818496 + d *
    (-6036090212479099769412939938011675532677900402688 + d *
    (6745972254750473649373170511083184763247249588224 + d *
    (-7152174741475204822152914448517988870426485063680 + d *
    (7163330442472319532141636629280014853889485176832 + d *
    (-6734563142574430481081377238026474645229630914560 + d *
    (5882144055979779623405434571832222890651757838336))))))))))) + d ^ 12 *
    (-4685803284290554351830504454221293863601070145536 + d *
    (3276852314376482739697665039539091102496565231616 + d *
    (-1814424097852497684710795112066419444667274231808 + d *
    (455786121544509740473232558202698304000904921088 + d *
    (671568557506429249925592519843043099087018131456 + d *
    (-1489161897553739171634407477265913191832709496832 + d *
    (1974211228266139246572266481362375266443176443904 + d *
    (-2153810068468245118674724501788155776801664925696 + d *
    (2090086928174512869982160841713949291668515061760 + d *
    (-1861609307364522884031866581711543282680399659008 + d *
    (1546160238602297287994563948236152215970971385856 + d *
    (-1208407073361707250871265822355415624493142376448))))))))))) + d ^ 12 *
    (893783496027391956008864636945796391866470760448 + d *
    (-627967604372815866975221522696680920746830856192 + d *
    (420176807188146592393063126750867434966484779008 + d *
    (-268209079600682891929604882429279039544611307520 + d *
    (163520020629328845559114483557922215355712012288 + d *
    (-95289971069037289903109944051960729742077591552 + d *
    (53097681935295798486350152624278336100758454272 + d *
    (-28294565859410801075369941221724459065874055168 + d *
    (14416646660082210849320633774401824274442616832 + d *
    (-7020839491822807429302362981376745241183518720 + d *
    (3265917217687825139383187071246587189258092544 + d *
    (-1449897157716338984797631881695270171964866560))))))))))) + d ^ 12 *
    (613623238471085323203914626397718175185633280 + d *
    (-247229090314804156043130316698156594694979584 + d *
    (94667957318455672311100331434234455925456896 + d *
    (-34382693505345316967449245083489259411734528 + d *
    (11816011963312023816550873572028550502154240 + d *
    (-3831416179783934940314839916061061698027520 + d *
    (1168232251271304054039200936815375762849792 + d *
    (-333584956228158962223606995700770206908416 + d *
    (88763169876105815837005417233811731382272 + d * (-21874330034826027016729631088555639439360
    + d * (4953538958323309830891604623733520596992 + d *
    (-1020247297833968098977646934100739620864))))))))))) + d ^ 12 *
    (188421302123053956074394249167968927744 + d * (-30552922348557075768541859224659165184 + d
    * (4202292079322674241104869954328985600 + d * (-458434250694541771006644777550348288 + d *
    (33017802221043786080945835720310784 + d * (-153951632592764414627158024519680 + d *
    (-332186360256321673881186823569408 + d * (42756625236778509658926152155136 + d *
    (-2257400848447808613159422132224 + d * (449250896231983500925100621824 + d *
    (-243702128424654298887670988800 + d * (64700556520565709356119621632))))))))))) + d ^ 12 *
    (-9592763984220205860950114304 + d * (653236666449720732766699520 + d *
    (41753560645127478607085568 + d * (-14670813669347967788122112 + d *
    (1355405504486222546075648 + d * (-12817295697455777054720 + d * (-6804295903869752049664 +
    d * (236994994427609743360 + d * (12162171086362640384 + d * (4470743755305779200 + d *
    (-332560477467443200 + d * (-56485422641446912))))))))))) + d ^ 12 * (1578835375030272 + d *
    (344832647888896 + d * (16128613285888 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt0 (d : ℚ) : ℚ :=
  0 + d * (0 + d * (0 + d * (0 + d * (0 + d * (0 + d * (0 + d * (0 + d * (0 + d * (1 + d * (410
    + d * (-121399))))))))))) + d ^ 12 * (13650907 + d * (-956411546 + d * (49072823403 + d *
    (-1980788484054 + d * (65074973839702 + d * (-1773239509520132 + d * (40627693323411652 + d
    * (-791988865989015012 + d * (13279759544126200508 + d * (-193476246290197519679 + d *
    (2472254909075673229808 + d * (-27945770088035522844856))))))))))) + d ^ 12 *
    (281634849274034158187665 + d * (-2548319093688465940868794 + d *
    (20832261375560395098822405 + d * (-154718506103942735319820642 + d *
    (1049060376268269365893681791 + d * (-6522250506002527267045261041 + d *
    (37326215147814724113084279931 + d * (-197314991170456374815891585800 + d *
    (966511983060565786204223002351 + d * (-4399629067401143670390634970215 + d *
    (18662107833503336742282408215056 + d * (-73951930369289540729676006604791))))))))))) + d ^
    12 * (274436737285772497179265453367356 + d * (-956011964135558836755283152101883 + d *
    (3133366083436845491624043495407748 + d * (-9684175979674873140136001786465075 + d *
    (28286110794309181177878687870986686 + d * (-78247611503993009396525793892153041 + d *
    (205422185762843448309517043796080143 + d * (-512793076842909099938174993791680423 + d *
    (1219350946161850235077460715532950309 + d * (-2766287676145537127234244039195294981 + d *
    (5995724964086447898729184440955434965 + d *
    (-12429378214754797135688292056575490389))))))))))) + d ^ 12 *
    (24665955071283657733298137091523912319 + d * (-46887410934434770765726467410636760425 + d *
    (85406524532219226876012848497179046970 + d * (-149099473477743656415154139680626302811 + d
    * (249460982346701035033048891300156893827 + d * (-399934106621350535423619613748151868348 +
    d * (614163898943235760487826743482345709771 + d * (-902974364802081736611879881566442304920
    + d * (1270214870738085907544546522330938079433 + d *
    (-1708137493002441242047254013716802821450 + d * (2193518323413974978536096468810311385663 +
    d * (-2686094960854707282895345758900930927135))))))))))) + d ^ 12 *
    (3130802096497474994670655660552948327076 + d * (-3464579093242889080793033499144421938363 +
    d * (3627243742324389478296504008825942883420 + d *
    (-3574401540011746973811765653430277614039 + d * (3289143809607383894789336718412338314226 +
    d * (-2788969623687148708974081506493389633285 + d *
    (2125291256651593037357876921244010132861 + d * (-1374917113961061479795243669757908400719 +
    d * (625394518025289517110629935642756161065 + d * (41909954253361351994668520684085329926 +
    d * (-566427139346884613143253748640738338223 + d *
    (917032693428204120395040987495812968420))))))))))) + d ^ 12 *
    (-1093144807116515423656057504188082954246 + d * (1119089178434079032030256412857132040783 +
    d * (-1034340876488626309191978329153333738407 + d *
    (882895148864811071785046228260065302818 + d * (-704512698727695249182829374536443150390 + d
    * (529367592954782205868900330421419820209 + d * (-376290062573227243885465080169522587420 +
    d * (253811036778761182461436869719124304594 + d * (-162781101458969089995859993562848664084
    + d * (99398074197143743295852136724258363811 + d * (-57833084181584522316815376332546963307
    + d * (32074390932807281652988759203563135141))))))))))) + d ^ 12 *
    (-16956109105229772148018101714259198352 + d * (8541606760770454051352657267756598886 + d *
    (-4097534890608587796166916053250688070 + d * (1870094570623995608375119355752498236 + d *
    (-810976499196578742692640091275234842 + d * (333617483494792952625940344884552869 + d *
    (-129928789799349946709861014411202056 + d * (47786084804344703382775346879212116 + d *
    (-16547398514800919577031636056840673 + d * (5375351917612989093308064690508108 + d *
    (-1630842717778527177041548866497405 + d * (459622954110653473382184416498327))))))))))) + d
    ^ 12 * (-119533050863555041141145294099218 + d * (28448385316840362361956258577983 + d *
    (-6130383366375970728116075636482 + d * (1179438063079057643230809551462 + d *
    (-198704834570269297970529061006 + d * (28497122637101805966924061763 + d *
    (-3327393128390990556265585938 + d * (293060924118216968829377132 + d *
    (-17130238593230233524054613 + d * (783817192499879554454659 + d *
    (-149813470385115455234091 + d * (26501130522843751275381))))))))))) + d ^ 12 *
    (1711914551258582000563 + d * (-1805386417627497032366 + d * (418147741835225923734 + d *
    (-52034657135340025657 + d * (2968182293720391042 + d * (118600243814230578 + d *
    (-31132476977125856 + d * (1344713067001136 + d * (16341958388576 + d * (9961076760849 + d *
    (-672055166805 + d * (-176848466067))))))))))) + d ^ 12 * (4970710567 + d * (1233507812 + d
    * (58451473 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_0 (d : ℚ) :
    orderSevenSelectionPolynomial d 0 = selectionExpandedAt0 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 0 =
      selectionNumeratorAt0 d := by
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
      selectionNumeratorAt0
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 0 =
      selectionDenominatorAt0 d := by
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
      selectionDenominatorAt0
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt0 selectionDenominatorAt0 selectionExpandedAt0
  ring

private theorem selection_cofactor_eval_at_0 (d : ℚ) :
    (selectionCofactor d).eval 0 = selectionCofactorAt0 d := by
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
    selectionCofactorAt0
  simp

private theorem selection_factor_at_0 (d : ℚ) :
    selectionExpandedAt0 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 0 *
        selectionCofactorAt0 d := by
  unfold selectionExpandedAt0 orderSevenDualKernelPolynomial selectionCofactorAt0
  ring

theorem selectionEvalAt0 (d : ℚ) :
    Internal.SelectionEvalCertificate d 0 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_0, selection_cofactor_eval_at_0,
    selection_factor_at_0]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 0 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt0 d
#print axioms solution
