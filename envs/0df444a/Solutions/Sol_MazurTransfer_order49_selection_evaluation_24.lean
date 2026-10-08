-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_24
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:56:57.068+00:00
-- url     : https://prove2.me/submissions/87a934db-3b42-4798-9c6e-8e1d0635c852

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval4.At24. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 24

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt24 (d : ℚ) : ℚ :=
  -65773314808020467712 + d * (-8841300346253869056 + d * (15886451173076729856 + d *
    (-35003813414762281024 + d * (55607654282041579392 + d * (-35951963442141719040 + d *
    (991625843504610624 + d * (19992700404686299776 + d * (-29345315043784194048 + d *
    (30881074716971294272 + d * (-22396150801221530304 + d * (11402660187615278016))))))))))) +
    d ^ 12 * (-3189581458441586240 + d * (-2308013335460682048 + d * (5490968249689020672 + d *
    (-6268067685723734592 + d * (5500778845459969920 + d * (-4223538404718626112 + d *
    (2929211941259558272 + d * (-1840408263602183040 + d * (1067548750699870272 + d *
    (-583705420252174272 + d * (297591384352001280 + d * (-138254840788627968))))))))))) + d ^
    12 * (59054057999203392 + d * (-24068928925411776 + d * (9340952061148032 + d *
    (-3224564861166272 + d * (940524725136384 + d * (-254779849224000 + d * (81431441760960 + d
    * (-28768839691008 + d * (8078103441024 + d * (-1518550945536 + d * (260385318528 + d *
    (-93540355584))))))))))) + d ^ 12 * (33322054656 + d * (-6017115840 + d * (352010304 + d *
    (-50877376 + d * (49836096 + d * (-10580928 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt24 (d : ℚ) : ℚ :=
  -77950821769754443776 + d * (-11172521325172359168 + d * (24421629916638609408 + d *
    (-56159081144569651200 + d * (91420091254589970432 + d * (-75267538230834326528 + d *
    (32654977894389405696 + d * (-3792206625740374016 + d * (-14052685870552103424 + d *
    (27890294575490301952 + d * (-29057763556610957440 + d * (21929539873268970560))))))))))) +
    d ^ 12 * (-13944000046659993984 + d * (6834864861709953920 + d * (-1223055170238907648 + d *
    (-1632107845377691072 + d * (2231246900402686400 + d * (-1911202563038330432 + d *
    (1380925269342303808 + d * (-880287371613975360 + d * (521804667544521728 + d *
    (-306192417062812608 + d * (175916879314441856 + d * (-95058870454546048))))))))))) + d ^ 12
    * (48977024547946432 + d * (-25019614867009728 + d * (12559582846315648 + d *
    (-5980942667558528 + d * (2691975617245120 + d * (-1162408274405440 + d * (476679526034112 +
    d * (-180805519622976 + d * (63338716886592 + d * (-20913546754432 + d * (6430072784768 + d
    * (-1705036914688))))))))))) + d ^ 12 * (346883196416 + d * (-45385710080 + d * (1981056000
    + d * (394164224 + d * (-51688448 + d * (-1336320 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt24 (d : ℚ) : ℚ :=
  58698389268754837530338251622956617384772648649378771238912 + d *
    (-2717932056391061742573024611557999635363082490864024445517824 + d *
    (1166081809557045897215595849585200268469828693284883638779904 + d *
    (4118621959981648002408676449529797603752433975200513079115776 + d *
    (-7844878852569152477784156903356277341455550503067398535380992 + d *
    (11382021726040245031291527390227302370800118442230354181881856 + d *
    (-5942115985317985803033663860845843173543547852791711560368128 + d *
    (-10185291654865811843693698055032042741533704860150747078066176 + d *
    (26456680185509077182765223954562041382955290099714474706468864 + d *
    (-33786212308237557887029350769530135267456555665882258828165120 + d *
    (25817125684513745504549284993851638260977166217615374600110080 + d *
    (-671970228507827172295077546369920114899156984053470124834816))))))))))) + d ^ 12 *
    (-31570162525136418700899749955319905780901309946648954092912640 + d *
    (54822405664969189748704171014423773700070576942314598258966528 + d *
    (-57973250606989656882730686565654690345497455383468372908310528 + d *
    (37779589524127222913091861682390525559304972560809944008622080 + d *
    (-279423454057900572848383213583196500445033809053713590648832 + d *
    (-40391500953343829728623735780296793191757303455439427351871488 + d *
    (69251794919250047757510376095438195920172289941489538258960384 + d *
    (-77145747097129288434171847062868997781696395477462043377532928 + d *
    (62880266187327283567104800688349587372924797746296393112223744 + d *
    (-32704935166853686733593151072019016045329705076909064381005824 + d *
    (-2614545780643760965461996280123390968743575236244074880565248 + d *
    (32446887878695451224911396343471181258692469473857745598283776))))))))))) + d ^ 12 *
    (-49862634350230158873003010489688548178898786000416871407157248 + d *
    (52870173866255892512036526736007007158519183272105484101615616 + d *
    (-43881213586195737642613259233002126009048064406771610833649664 + d *
    (27964083349114111172944768426176863399844866415733837786513408 + d *
    (-10635676467808604566192799139159664836141441826992305184178176 + d *
    (-3828514168725304079730573615447722710721627414820261599117312 + d *
    (13145958035583650960807609085801473973660498746536993989591040 + d *
    (-16982947845753873609893779737874411314282754635261879467900928 + d *
    (16393126639754234426902663070914044279827184730192477321428992 + d *
    (-13060457734904556149778526801194425210273592340995082069999616 + d *
    (8652556664609927669809728153323585066172400056868879180234752 + d *
    (-4433607986829315995646579383478024053632671294967831037214720))))))))))) + d ^ 12 *
    (1131490193225289046266129497662129338615767718538427783446528 + d *
    (1010505310943706733211565346132718217405157987802671116713984 + d *
    (-2084929460828243669826765556459095501262666517862397741891584 + d *
    (2355499499796285987670978389504126557504844984822814669799424 + d *
    (-2126315848840019088094799973094718325453664300288087476404224 + d *
    (1660897191045251188140667845587202343343154625268042961518592 + d *
    (-1146986443836502564486307333898249510817962793722988435341312 + d *
    (694213607800978122050569450512471067670129499333537696317440 + d *
    (-349504006989205565236079922466870345698481536492591780200448 + d *
    (118039173553444515676855118017593299346924892065956872323072 + d *
    (17506509118871517479643767316607287336003908951417686851584 + d *
    (-82661502889950559905478149878963828157686447446245106515968))))))))))) + d ^ 12 *
    (102347824704806668140717758936884937560985636088584546025472 + d *
    (-96634052315082435174347955461530436829218547655709481500672 + d *
    (79584591009793207616809652948534972849471267840325684035584 + d *
    (-59842899190440252025344518563209048994541106041193165488128 + d *
    (41936162220009647441680353775477742945457395655486929108992 + d *
    (-27664039183496961589058404105251073036915585948745628385280 + d *
    (17251661509580812789952893207427791375778334684515410378752 + d *
    (-10168452552076457702407790222244177820848083827256000774144 + d *
    (5636518853387404396750223290685892659392644527243312496640 + d *
    (-2901956143195920366333660409284985416117099468147780747264 + d *
    (1349577091032545296419184084361537360192308628392282161152 + d *
    (-527853637978983117348424888600609746345645543041390084096))))))))))) + d ^ 12 *
    (130646287957320384303955347679490340823928353580312952832 + d *
    (36057365756626968334184071027191016696329088215488135168 + d *
    (-87609261161408078073910335467295011486467195304549548032 + d *
    (88162092654721366854700707526354016975499995680569294848 + d *
    (-70706232160016994572456272921853113440766673926957563904 + d *
    (50497013830019925751999579924275235518638416953503645696 + d *
    (-33427538047858813112770948637266023075542893832609202176 + d *
    (20902605599445176080017541500880096810207298990830518272 + d *
    (-12475023360337739377831153581826785644792131605155807232 + d *
    (7149639498314472972528236946979856746283316505794576384 + d *
    (-3949731188463326573036385255407172811432788335198994432 + d *
    (2108154740884609980465222195798971388841670418354405376))))))))))) + d ^ 12 *
    (-1088609317556953993121905485626365502230980675274014720 + d *
    (544169083868733921122950076604524509998535272518123520 + d *
    (-263308644924068014254315022049884858936255124340211712 + d *
    (123243603551819645778308984842408059809766474832412672 + d *
    (-55719696345909137793726602290750609494436407091396608 + d *
    (24274527189355651231321931289172643169032940341166080 + d *
    (-10151220411438276870606455825975950941032456872001536 + d *
    (4049720602313559991477696548111166187460335391473664 + d *
    (-1525308145110501822810407054242251784335324137127936 + d *
    (532170849213970616485245049903511705346413951713280 + d *
    (-165192096136443526686696333379117469345929319153664 + d *
    (40775375187636572837552527870757993276333828866048))))))))))) + d ^ 12 *
    (-4073647305002123792931148386923317991806359830528 + d *
    (-3875013307926765979258940060377370714872526667776 + d *
    (3873488072476469427992261296049589155267953295360 + d *
    (-2471704205226898294697850216647577508672808157184 + d *
    (1331810100822821829086176977144400338672573218816 + d *
    (-651097408631000041663749666278384524077584613376 + d *
    (297394037332383389280863258885413589014410166272 + d *
    (-128784557595437920236998935185896653386159226880 + d *
    (53307865287253710526742709169210872056642535424 + d *
    (-21193977364676204843666227831634278249031532544 + d *
    (8116747719454277146772891949437553754723319808 + d *
    (-2999238650010610797756058084964562423691870208))))))))))) + d ^ 12 *
    (1070087510950372489672556117579611936207667200 + d *
    (-368653055707438585654892353658977140146962432 + d *
    (122563049031720461690681718898782410053779456 + d *
    (-39280098796879700016837012802539646405836800 + d *
    (12116307299998545175134467666510632008810496 + d *
    (-3589437022263362201383585614276499103285248 + d *
    (1018384763758280248434138960865292526813184 + d *
    (-275680039167183758420222947598661624528896 + d *
    (70857166274245696741588772780859021066240 + d * (-17182386232528045989115078338631200931840
    + d * (3898349646002480276720749438064818913280 + d *
    (-818292554817892731809570134729310601216))))))))))) + d ^ 12 *
    (156443532317744159313274772564567130112 + d * (-26613738914779843186393985706234216448 + d
    * (3877481296071759822028991068147023872 + d * (-448760682924007672468901212426338304 + d *
    (33113880751619385788256625403887616 + d * (476049571368707997404996741627904 + d *
    (-571957955262275744466111892291584 + d * (84969936786587077437048740642816 + d *
    (-5429141761704210189662236180480 + d * (152310371769388066012754083840 + d *
    (-133136995062602775438633730048 + d * (52263651922348739814871793664))))))))))) + d ^ 12 *
    (-9329275333779532269731708928 + d * (740673413895024872324071424 + d *
    (34277399300108718523809792 + d * (-14884435092105713881186304 + d *
    (1369813130507432168259584 + d * (-6250288105379117662208 + d * (-6886274268618501652480 + d
    * (154294322420560691200 + d * (11670867988901003264 + d * (4932483473541431296 + d *
    (-303334455845060608 + d * (-55379370483122176))))))))))) + d ^ 12 * (1610481876860928 + d *
    (345176413044736 + d * (16128739115008 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt24 (d : ℚ) : ℚ :=
  2132518595443004561627722178335785628857740034048 + d *
    (-98472902249424913414858116522819605493887344312320 + d *
    (29372973261931990628489853277924837196003348054016 + d *
    (178207408634089824593462711693885112129327879684096 + d *
    (-287725775432033137681953944304591850909010485051392 + d *
    (340727816868120977582516653400454574581806077575168 + d *
    (-62872290613091537799037476644455104141592155389952 + d *
    (-526815571372158929474686721535364169374732700614656 + d *
    (971251169759103154953569459212045269055564587836928 + d *
    (-967273183793412989603458088994145408555133857559879 + d *
    (439836873729869596174091627901160240828814679150698 + d *
    (490135910478989850083174035167452483656277472051041))))))))))) + d ^ 12 *
    (-1372591630978099411583343249051535776419370414927821 + d *
    (1714763342471766896061561100480810204364331227353342 + d *
    (-1348956844552409122477318001887438181981039820416277 + d *
    (414332014542608757404239809425328674031399613412346 + d *
    (740035776813085588208600241329643590522633611970662 + d *
    (-1667801480327337973145307232964059725467333779573052 + d *
    (2045262844020139499910636382649532728899302440591452 + d *
    (-1803386925393569925846344361743023023734121028329972 + d *
    (1089481821137415940932354227364183531898877009800340 + d *
    (-176527632921155603685934435528338736413136832074271 + d *
    (-642014629311384501692237240443941459728276475789160 + d *
    (1160417678641342633076670441169628394758269254742376))))))))))) + d ^ 12 *
    (-1310631294601360491298071044477415624142431849975599 + d *
    (1143557310204085746694163573327446255184764779962078 + d *
    (-781107657587322780077033913881589674388725124771339 + d *
    (362508520759000308666526072238670606992641141627478 + d *
    (1110380921925761309517346366419050343448561779591 + d *
    (-248606600858536491674081908327147736630943246248049 + d *
    (367020151189789555320413890883637294091310403231475 + d *
    (-377422722457066885441144432817440718465316298900840 + d *
    (317345023477877159972574688166021817416003363718991 + d *
    (-225312657203665234877295044434682011431394182619087 + d *
    (131293512941757322917591240121242394183214294585752 + d *
    (-53466760240764581548319404417957091962518864821127))))))))))) + d ^ 12 *
    (-791605674856583998907691173751633893736916800668 + d *
    (31877854985466167098397039949690980777383278036501 + d *
    (-44458151032523143241001107447682114724397571995652 + d *
    (44578869621867453876406989209253935119479955064725 + d *
    (-37830595338382592514568879324545297194564660439170 + d *
    (28472495564211433128820154910641897178159638107887 + d *
    (-19239066125329269946423713617695817980167833960753 + d *
    (11549008412139188606138877382919426528087597178633 + d *
    (-5877049968205747264086357978727715599325499971139 + d *
    (2126990479568648221283725683201120328397293904667 + d *
    (70611112262650762792729778283992932121772211781 + d *
    (-1156802936964579639453936150781276454744293136173))))))))))) + d ^ 12 *
    (1530635998083084634518949319224101720919073204287 + d *
    (-1501544162135109846289860168077092834180929204161 + d *
    (1282794495082269975182089780707533877536462203634 + d *
    (-1005738591577389925895113360782868179183231926283 + d *
    (741224739760828489482743548451558343292640776619 + d *
    (-520291322539597360690098180331507655931796280980 + d *
    (350617280949594814072771491567589180302990660899 + d *
    (-228009569904441691468608037248483959002448610704 + d *
    (143588293930955817359581324850299074124969592265 + d *
    (-87775550607248157661630987071959317252952181426 + d *
    (52171821818539090570836209445964742542454532199 + d *
    (-30184902112487892948540928773227199963138581391))))))))))) + d ^ 12 *
    (17011294184395621356263452131614675559206882756 + d *
    (-9341953845842246027833841265745083804651802827 + d *
    (4999535883538234198223045418607201990955085420 + d *
    (-2607008217254635798495158807585935140945700799 + d *
    (1324024002826616202507383860712905216490447850 + d *
    (-654475038792241910861704870267572476704738709 + d *
    (314557620723133417917769012067300752454282101 + d *
    (-146794070745933279572751176201267282740164911 + d *
    (66385169882298539666409295977045297183091145 + d *
    (-29013312089909855393292883694134895258302394 + d *
    (12205781797058023374976993008878834660006849 + d *
    (-4913248765893141323471315979412954060933388))))))))))) + d ^ 12 *
    (1874117824355679713582360144406756172823906 + d *
    (-665905198262823761573729636898194420232809 + d *
    (212874112249686374526474064773189267243737 + d *
    (-55956125415915330988739483651004379254230 + d * (7943349373189002781043921806590870471450
    + d * (3450817931077389291828245880411213723121 + d *
    (-4233977158115337343281717101899145981388 + d * (2849678082204038301655428654241577964970 +
    d * (-1579627851222866452018641612635918915084 + d *
    (787588033745489458976581093003690314275 + d * (-365402752660125923666400284774456195715 + d
    * (160375350872576322906005586818759373077))))))))))) + d ^ 12 *
    (-67192464849016421843594278282063448552 + d * (27014186673719383697665133994727844422 + d *
    (-10453789074973478465278223901784634158 + d * (3900303195654713862076438530646759716 + d *
    (-1404110122978503623311604905214046890 + d * (487760427407447659140279697523008477 + d *
    (-163394997369257931679806857274669568 + d * (52711183255314922425122144042392836 + d *
    (-16341414514523897115899719016439889 + d * (4855358894806324022000135353744996 + d *
    (-1378066366714893259206053428973117 + d * (372074381476701071992241105735303))))))))))) + d
    ^ 12 * (-95006118706696918380104290680586 + d * (22739968636015682447307526441959 + d *
    (-5035137312834286455903835298362 + d * (1012165575456594904621670228006 + d *
    (-179959407705553814011586156422 + d * (27256439203719877246509047891 + d *
    (-3307323877430098769406770610 + d * (282114101867607878204397308 + d *
    (-9936089480809035509544109 + d * (-1015035553949808559478693 + d * (93294586688372866547061
    + d * (13324458126832388413725))))))))))) + d ^ 12 * (270676552276961201539 + d *
    (-1472186671122980633054 + d * (398078345504316823302 + d * (-52706465818563343753 + d *
    (3024612734064675402 + d * (131210024089959378 + d * (-31043473883135864 + d *
    (1127381943673136 + d * (13942311205040 + d * (11406121002681 + d * (-575566319277 + d *
    (-173219954019))))))))))) + d ^ 12 * (5077438039 + d * (1234727012 + d * (58452121 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_24 (d : ℚ) :
    orderSevenSelectionPolynomial d 24 = selectionExpandedAt24 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 24 =
      selectionNumeratorAt24 d := by
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
      selectionNumeratorAt24
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 24 =
      selectionDenominatorAt24 d := by
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
      selectionDenominatorAt24
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt24 selectionDenominatorAt24 selectionExpandedAt24
  ring

private theorem selection_cofactor_eval_at_24 (d : ℚ) :
    (selectionCofactor d).eval 24 = selectionCofactorAt24 d := by
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
    selectionCofactorAt24
  simp
  ring

private theorem selection_factor_at_24 (d : ℚ) :
    selectionExpandedAt24 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 24 *
        selectionCofactorAt24 d := by
  unfold selectionExpandedAt24 orderSevenDualKernelPolynomial selectionCofactorAt24
  ring

theorem selectionEvalAt24 (d : ℚ) :
    Internal.SelectionEvalCertificate d 24 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_24, selection_cofactor_eval_at_24,
    selection_factor_at_24]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 24 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt24 d
#print axioms solution
