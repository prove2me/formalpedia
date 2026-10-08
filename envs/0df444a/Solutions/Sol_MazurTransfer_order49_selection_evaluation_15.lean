-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_15
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:59:26.874896+00:00
-- url     : https://prove2.me/submissions/b1c1e732-8e56-4483-8b8a-9c29a665f58e

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval3.At15. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 15

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt15 (d : ℚ) : ℚ :=
  -239483061000000000 + d * (-63311454252000000 + d * (179121286868112000 + d *
    (-391387663587663424 + d * (531272178522342144 + d * (-250305315915163776 + d *
    (-321598224164466240 + d * (835278448528832064 + d * (-1125546503606573376 + d *
    (1086908072371986112 + d * (-673944224366319168 + d * (73427872690833408))))))))))) + d ^ 12
    * (504249190038428224 + d * (-950884855702014144 + d * (1207058331566338944 + d *
    (-1253506668586676736 + d * (1137035217935323776 + d * (-931396574913703296 + d *
    (697539110830312576 + d * (-480378711069996864 + d * (306896063447255808 + d *
    (-182883307959343488 + d * (101086986617511360 + d * (-51409520279245248))))))))))) + d ^ 12
    * (24136434658710720 + d * (-10560617789659200 + d * (4266464953682496 + d *
    (-1539297944797376 + d * (489410106249024 + d * (-148660337330496 + d * (49842894877632 + d
    * (-17491055295936 + d * (5106356369088 + d * (-1095110446656 + d * (222190824768 + d *
    (-75104356416))))))))))) + d ^ 12 * (25835721024 + d * (-5047054656 + d * (410216256 + d *
    (-70224064 + d * (48550464 + d * (-10601664 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt15 (d : ℚ) : ℚ :=
  -283806716625000000 + d * (-81664386510600000 + d * (269610520216032000 + d *
    (-632265015403484160 + d * (971921632935618624 + d * (-803381638789533248 + d *
    (175515063245708928 + d * (485784391436066176 + d * (-1035525854496253824 + d *
    (1389523566682919872 + d * (-1346945819073383296 + d * (978062643930006272))))))))))) + d ^
    12 * (-481621480335589440 + d * (-17100100496731456 + d * (407529556175049344 + d *
    (-601534176227628928 + d * (615249311905352768 + d * (-526031990271936128 + d *
    (400041568217780608 + d * (-279566345210836224 + d * (185869926214988288 + d *
    (-120427055565174912 + d * (75871909806239744 + d * (-46054730292525568))))))))))) + d ^ 12
    * (26992767753002560 + d * (-15324596382303552 + d * (8366358991863808 + d *
    (-4350722423130368 + d * (2145861200724160 + d * (-998440527599296 + d * (433680658890624 +
    d * (-174523273344384 + d * (65073823277376 + d * (-22356272063872 + d * (6857561898368 + d
    * (-1764435481600))))))))))) + d ^ 12 * (347666422784 + d * (-44756957696 + d * (1995128832
    + d * (381648896 + d * (-52951040 + d * (-1345536 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt15 (d : ℚ) : ℚ :=
  2826375596328794644420318072265625000000000000000000 + d *
    (-128172329608713246815321246701500000000000000000000000 + d *
    (-21621647835409323776138679051310320000000000000000000 + d *
    (525745912342451184927157572816045118416000000000000000 + d *
    (-1019457942229784471827650296336039593028160000000000000 + d *
    (915012235671319725051773312252312801977843200000000000 + d *
    (1391667839110943139141075169028981805105837772800000000 + d *
    (-6228985973638276000703076819582126517677916736716800000 + d *
    (10542644645440868811310595480291268536992119307468800000 + d *
    (-8715310088806793408950253136988018675780488511743328256 + d *
    (-4919227284751577110016117148651112923455145246439505920 + d *
    (30727111317000037046781095789833471842454267127516626944))))))))))) + d ^ 12 *
    (-57620938797793136576328960632226584324435009160770748416 + d *
    (63905912576798996977020735295248945504246770764878708736 + d *
    (-26986414270412419615401198097833717024126381703081492480 + d *
    (-62004019660794059736640889979504978170820124889284870144 + d *
    (184058932090003268249977277861674592610484774907362148352 + d *
    (-288800847422649207242938142566553445828059939135981092864 + d *
    (309314823902722926703742592292583630809631692100259020800 + d *
    (-191323415603657654967434949076183221216622089700922884096 + d *
    (-75265372627463095995349346695786318523201971812436541440 + d *
    (437086217160056914677063303507804104567297631778198781952 + d *
    (-783304572639416822148490302748181299540992247160947081216 + d *
    (979181667921133937246989923569407570346704308355372679168))))))))))) + d ^ 12 *
    (-915387206045649783427884908682322906883485203999648382976 + d *
    (553660008027763518541035838172643011185575191017575415808 + d *
    (49994104298544901393237859708866414411337935447854940160 + d *
    (-755470995487506250878580779892749397939402543157606875136 + d *
    (1379376275291490407678193770805344267590502201415593361408 + d *
    (-1751245249467873308669445922561747852897150109513167929344 + d *
    (1764926115422447160046940801780354925862995717105341169664 + d *
    (-1407964845108673285413548314706593432065238268353071808512 + d *
    (760815790313568264762463903866765659835721156947045515264 + d *
    (31008873120698469852611078938890772029542175043171385344 + d *
    (-800003161685813467085294649167875371976060269989459656704 + d *
    (1400061088746288378223692709003925093501587823359890554880))))))))))) + d ^ 12 *
    (-1737792744059956071317789662857341175582473448726721986560 + d *
    (1785291727624833128509261554416867784012894097067085922304 + d *
    (-1574650766638737784409138679285015403204140049676162826240 + d *
    (1179641769893032737162727217026391513372393515771135524864 + d *
    (-692141516567043459432768697422796654342186781271432626176 + d *
    (200278482186729722252489145014243745833349752473497894912 + d *
    (227079842587695208494572308392993798994348878978585722880 + d *
    (-547786135493652528911995741553539656753620777326866071552 + d *
    (746557387655361740602696721337722343658516759495542571008 + d *
    (-829998500111053834848074986277653940588453160041274408960 + d *
    (819125195744069928005124012271361891902833403673816858624 + d *
    (-741670066007300935109643480089455078635802687944917516288))))))))))) + d ^ 12 *
    (625717900839331713270204424037548863015037255748121001984 + d *
    (-495402222685812059588434845167701750475098236864331513856 + d *
    (368723927285537101678288955251946040355388178061291945984 + d *
    (-257120195069895950897426620787712866838520413666805547008 + d *
    (166217863633034576275148965370645035443293587001646776320 + d *
    (-97198858429318220739699488193638459391843999011527196672 + d *
    (48314564229515407847483652713174479304177988862002855936 + d *
    (-16242316306171515508034499935456277878303704918389161984 + d *
    (-2870850672379759019345077114863247147539718446848147456 + d *
    (12713604211748938494026113714377592103921484538888323072 + d *
    (-16426183856304712958665661440207635974514541854622744576 + d *
    (16452701239267934236619000403162090208618172178783010816))))))))))) + d ^ 12 *
    (-14549543956084833846600191579417648152324485048432066560 + d *
    (11880268635771178678856389111854545056408614641727438848 + d *
    (-9145131501163113707771248640773495556760224667491893248 + d *
    (6711624206195823512287277886910157897074416944588521472 + d *
    (-4727592020395132442713508521348650085510990328870993920 + d *
    (3209532251388709892916728763374023176726048969648766976 + d *
    (-2105680145838993438576432521534325542490695384964005888 + d *
    (1337275332631267308017370137157073759995533022126669824 + d *
    (-822900863344099391787250182123487377319494536472821760 + d *
    (490851118185438977759110375856445412038410258571067392 + d *
    (-283785670869275191555131653249974150830245478959677440 + d *
    (158934403823988795578760290842392434509837299529547776))))))))))) + d ^ 12 *
    (-86126584994398323648308195990723227865864407762599936 + d *
    (45075841924091318855634391943351213718820892433186816 + d *
    (-22719450365386539099488987219149774062414514398691328 + d *
    (10979679322308972481864923783383647441797924135108608 + d *
    (-5052247665984172822311247366014353188808241816797184 + d *
    (2187534573768925694744729679964042748343042009202688 + d *
    (-871816483383763440247106445489942000754733608861696 + d *
    (304631677010356887387735042620253765403641019367424 + d *
    (-80481898065741914548388797791489702630924842434560 + d *
    (3481881926195789424980058796968820279748310597632 + d *
    (15906712138185477624794433424289592771953403887616 + d *
    (-15880285298559179031414470559139124423341124354048))))))))))) + d ^ 12 *
    (11237989281325353527462039377878314966586452082688 + d *
    (-6860084135369398595510127769908910097148666970112 + d *
    (3828427093590174340610176163665795191941946933248 + d *
    (-2002891487355822819040174654552577693070131200000 + d *
    (995128625968043926255568713455449628281981370368 + d *
    (-473060645223053082301052179097953932506891026432 + d *
    (216135681179332941196214402427271318713313001472 + d *
    (-95172839874476632283380030873632165201991958528 + d *
    (40457417545380984715451986546740456872198275072 + d *
    (-16617565270725656679594084564442431290905722880 + d *
    (6597104660513270132109911581646231814291062784 + d *
    (-2530944426264798583087022902027022093948026880))))))))))) + d ^ 12 *
    (937779267546244158411501065279342668982517760 + d *
    (-335261591585521774549952708090418762905288704 + d *
    (115489139470408873055555200826922497140064256 + d *
    (-38265299721588300594766763275308428557549568 + d *
    (12167693400788824106058810622827049359769600 + d *
    (-3702906977539046339031511402684016849059840 + d *
    (1074737933707792418193252092501140312686592 + d *
    (-296214825877979255672725751479356621848576 + d *
    (77108299294696494015897268880900716756992 + d * (-18828711689383087058150305067716032593920
    + d * (4275427169624826872329026484907775885312 + d *
    (-892520827545410020868056389770337583104))))))))))) + d ^ 12 *
    (168639038735118236212572874476717604864 + d * (-28189602037601841857980864696741003264 + d
    * (4016695393181360812350454809936527360 + d * (-453505990090590716761226535392247808 + d *
    (32849233993362559143453122493415424 + d * (314755997625746036728619610931200 + d *
    (-491564553165902106046087109541888 + d * (69453696206341148558165114617856 + d *
    (-4155738101107769058821713690624 + d * (251667257767537066568810758144 + d *
    (-174455374256650851563850956800 + d * (57002022190909813086137352192))))))))))) + d ^ 12 *
    (-9426917726495707487216861184 + d * (706946758344781739137433600 + d *
    (37043227804369289150988288 + d * (-14792933096632182348972032 + d *
    (1364887121618461588717568 + d * (-8771324959395876700160 + d * (-6860979119812226842624 + d
    * (185072902063327805440 + d * (11848288501722251264 + d * (4759244392061992960 + d *
    (-314294378797465600 + d * (-55794140042493952))))))))))) + d ^ 12 * (1598614438674432 + d *
    (345047501111296 + d * (16128691929088 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt15 (d : ℚ) : ℚ :=
  401092491311509308378495275974273681640625 + d *
    (-18107312000937990972722348034381866455078125 + d *
    (-6915413118505964706091147417430877685546875 + d *
    (80489337466961966158127851176794952392578125 + d *
    (-130420611081217758541751506948182187500000000 + d *
    (69296607044847888154535392694318940380859375 + d *
    (288502236603352871407246457351226524565234375 + d *
    (-888932071171619796938762408293733311630575000 + d *
    (1203412329415882266197769002633123310173887500 + d *
    (-523117721256929022720930677094273448559737454 + d *
    (-1559814024766639923043124209305403494708184930 + d *
    (4536851954104165444519262090962237255142800661))))))))))) + d ^ 12 *
    (-6561230546327190075914185292341817386340635448 + d *
    (5119464635279718858973516756143513586078260874 + d *
    (1392782947113332673618022113042266168341962903 + d *
    (-12185415196781213546414373160939599870083091474 + d *
    (23386072673299817750492754075781638676347651082 + d *
    (-28912672622701241445168481367049186308772420932 + d *
    (23062484530191633987884494360429219784042694697 + d *
    (-3598050022103420608908962111250681251990699727 + d *
    (-26239717717497592094361216836886820103212691677 + d *
    (57820653875813016336586844075592282472781400391 + d *
    (-79667292014633052582782418079757634144097517617 + d *
    (81655488527211468884265235875577331147956949054))))))))))) + d ^ 12 *
    (-59076217614811632515790525688087219965654146840 + d *
    (14855035624853567748194820409964324925021673676 + d *
    (40937141915484466845267720574920081145693349775 + d *
    (-94122583283799734726288656511829547768787539567 + d *
    (130830841713392449574407353979927991663764736391 + d *
    (-141611546571025138717452886384948423454227840281 + d *
    (123879489053066693574764680930124771759328831466 + d *
    (-82100974730253305716500271420091799644355176695 + d *
    (25951539079383888186750090754098347831980541161 + d *
    (32696793850693674102744092324416895709376052555 + d *
    (-82874791092907516778471256361272658809781886024 + d *
    (116826284898132309033548483340690450754624240284))))))))))) + d ^ 12 *
    (-131090292278082321024633276763672603439943411794 + d *
    (126361771464911915868850617035649048758756194572 + d *
    (-106466240939343495636046139890383602438547855867 + d *
    (76925476044028234912477650494288903131674173860 + d *
    (-43552967344358169027711012222772907727302452679 + d *
    (11374670450832750940341810686512197604581252909 + d *
    (15996965524495204966425624334362684129814418113 + d *
    (-36549479561574999776621520011498285442476165793 + d *
    (49721094151671254531924109678924814960645550244 + d *
    (-56053055253733188567978570963721587078922652181 + d *
    (56772581828844099523128094061450062204418473475 + d *
    (-53403694378182647942739739546844317494144909379))))))))))) + d ^ 12 *
    (47463496314340384140556804587696239506094951554 + d *
    (-40264787114156068361839680464793393855620280935 + d *
    (32818856295537908975407814850620957016552807635 + d *
    (-25816829952153428311140801627710878894059062226 + d *
    (19662565522991131205111983065124503576842006687 + d *
    (-14531924398179476789336059185902480939532756343 + d *
    (10439044428201272888908724381492317913846197976 + d *
    (-7297134594860541811222964847212769954840309290 + d *
    (4967448437165719351737736457175055247393789628 + d *
    (-3294625786961721256510171904898399004255256835 + d *
    (2129414098290112175420838387221537098319006428 + d *
    (-1341172446617917628942855365846002490730748465))))))))))) + d ^ 12 *
    (822950329122506441529184024578197774426732531 + d *
    (-491727329224100472068085890844557546054073468 + d *
    (285908687774154714001719478922567213243061375 + d *
    (-161601762549775776794470333165132500867734889 + d *
    (88670922936139094565195886523248300279764531 + d *
    (-47142335044038005844320736649644486749865290 + d *
    (24220988146469890400057318474499023713135981 + d *
    (-11980765354824943931097922072541172350790989 + d *
    (5673326499792924362591338763363550866923730 + d *
    (-2548918831092309997832616136444329833185109 + d *
    (1069769580377017429441944968637645103093877 + d *
    (-406743211310092176126605100859525878796865))))))))))) + d ^ 12 *
    (129918710602324591047947313515071341230804 + d *
    (-25751456371126527934593487264252647268622 + d * (-6745925000306618894351776362220678419637
    + d * (12584032814066181276151855733032541400463 + d *
    (-10325611824523736182020188211893592749760 + d * (6786837817739613444772725681773459982499
    + d * (-3974819531218008536922685241231053339650 + d *
    (2156292762408914574492680974018694629534 + d * (-1103594161868653353139704690193920306089 +
    d * (538211708160015784149542399323554323201 + d * (-251581464710393778778361497377686960907
    + d * (113115744757223008507622295677911718966))))))))))) + d ^ 12 *
    (-49023167662122453420620182664477121362 + d * (20502542864162896926161260242542795311 + d *
    (-8278081898648377173560599240882702270 + d * (3226361964944019536181667820346166581 + d *
    (-1213087554002728951285762630923447722 + d * (439536780878740616259560431823134249 + d *
    (-153227352622764987878857471744490896 + d * (51286447056565167159720874446486141 + d *
    (-16437538917020544071426560989443848 + d * (5027985588925064908446463818272728 + d *
    (-1461652165994791380813532093200695 + d * (401603270805966644289330879703622))))))))))) + d
    ^ 12 * (-103528922549795406121985451927493 + d * (24794636192865188314167487873428 + d *
    (-5444973767073466673212123511422 + d * (1077542642891292810900921525737 + d *
    (-187697147855411859671871084316 + d * (27817481300386849951292360678 + d *
    (-3318693587918841444017543418 + d * (285018831898304771995680362 + d *
    (-12368773787077735573919563 + d * (-360952559749320176783786 + d * (1538289897375662622474
    + d * (18459156109938820944141))))))))))) + d ^ 12 * (812890247716744376698 + d *
    (-1598822218928441535296 + d * (405491691108271767204 + d * (-52430021096336187607 + d *
    (3004837196937253167 + d * (126327630333981393 + d * (-31092834352663331 + d *
    (1208178032419316 + d * (14821247613671 + d * (10863949540659 + d * (-611750242305 + d *
    (-174580646037))))))))))) + d ^ 12 * (5037415237 + d * (1234269812 + d * (58451878 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_15 (d : ℚ) :
    orderSevenSelectionPolynomial d 15 = selectionExpandedAt15 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 15 =
      selectionNumeratorAt15 d := by
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
      selectionNumeratorAt15
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 15 =
      selectionDenominatorAt15 d := by
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
      selectionDenominatorAt15
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt15 selectionDenominatorAt15 selectionExpandedAt15
  ring

private theorem selection_cofactor_eval_at_15 (d : ℚ) :
    (selectionCofactor d).eval 15 = selectionCofactorAt15 d := by
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
    selectionCofactorAt15
  simp
  ring

private theorem selection_factor_at_15 (d : ℚ) :
    selectionExpandedAt15 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 15 *
        selectionCofactorAt15 d := by
  unfold selectionExpandedAt15 orderSevenDualKernelPolynomial selectionCofactorAt15
  ring

theorem selectionEvalAt15 (d : ℚ) :
    Internal.SelectionEvalCertificate d 15 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_15, selection_cofactor_eval_at_15,
    selection_factor_at_15]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 15 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt15 d
#print axioms solution
