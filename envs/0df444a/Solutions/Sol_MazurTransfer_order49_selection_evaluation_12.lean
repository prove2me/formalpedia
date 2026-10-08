-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_12
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:41:24.169931+00:00
-- url     : https://prove2.me/submissions/9c1837ce-7e7b-4497-9982-65bd32ddcaa0

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval2.At12. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 12

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt12 (d : ℚ) : ℚ :=
  -16726934666870784 + d * (-6216875445583872 + d * (20736525913731072 + d * (-44974737482167360
    + d * (56165171482597248 + d * (-12613662889640448 + d * (-79618896317870016 + d *
    (173799519013359744 + d * (-228231179539150080 + d * (206273771896178752 + d *
    (-90280211536148160 + d * (-88795555626268224))))))))))) + d ^ 12 * (280684968075827392 + d
    * (-444270070169571648 + d * (549155460116295168 + d * (-580485527078374464 + d *
    (545829696462926208 + d * (-466369402046911296 + d * (365417493098136448 + d *
    (-263923957774504320 + d * (176751251963059008 + d * (-110057183368485312 + d *
    (63442483934896896 + d * (-33666735562874880))))))))))) + d ^ 12 * (16461854253612864 + d *
    (-7439562211879872 + d * (3076558795380864 + d * (-1136707457836736 + d * (374187751637760 +
    d * (-118355319104832 + d * (40519799087040 + d * (-14297343700224 + d * (4257802568832 + d
    * (-959434745088 + d * (205718365824 + d * (-68535532032))))))))))) + d ^ 12 * (23394273024
    + d * (-4722498240 + d * (429618240 + d * (-76672960 + d * (48121920 + d * (-10608576 + d *
    (326592 + d * (122496 + d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt12 (d : ℚ) : ℚ :=
  -19821812200243200 + d * (-8103252746502144 + d * (31216940199051264 + d * (-74093280954986496
    + d * (112149174764279808 + d * (-86684543945944064 + d * (-12396001371684864 + d *
    (135372622946824192 + d * (-248445435406281216 + d * (318213451789119232 + d *
    (-299364112506481792 + d * (195900885072453440))))))))))) + d ^ 12 * (-45227031791010432 + d
    * (-115528982190705280 + d * (246250194096850688 + d * (-315184086165288640 + d *
    (320557225762533824 + d * (-282479792830974272 + d * (224412926298133312 + d *
    (-165298155564717120 + d * (116100941580094976 + d * (-79178241576814272 + d *
    (52472945585254016 + d * (-33615222917791360))))))))))) + d ^ 12 * (20778719306728384 + d *
    (-12365249194874304 + d * (7040575568199808 + d * (-3810905552819840 + d * (1950219380199616
    + d * (-936401428021312 + d * (418071959059392 + d * (-172644675588672 + d * (65775580038720
    + d * (-22848902902144 + d * (6998029791104 + d * (-1783945639936))))))))))) + d ^ 12 *
    (347974352384 + d * (-44546746880 + d * (1999819776 + d * (377477120 + d * (-53371904 + d *
    (-1348608 + d * (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt12 (d : ℚ) : ℚ :=
  960913371484881763644684090020274119167080136704 + d *
    (-42743831858608150496393740317853800611870089936896 + d *
    (-30487345899074762312898156713032137117467047624704 + d *
    (280626852787457731865976126620600631455500052987904 + d *
    (-506577380125173074765699509098922569771581586800640 + d *
    (139995071790964770557229713549441802282968832540672 + d *
    (1974351093782090917222167369183946222559670728392704 + d *
    (-5879673766208046268678567098047506281250181527633920 + d *
    (8152808016035130844589116463700289857188299655872512 + d *
    (-1668925302954037177247671356045858149225769392144384 + d *
    (-20798933026045842232217679011748792905108717231669248 + d *
    (57263883294174945063332612601281266467893126776750080))))))))))) + d ^ 12 *
    (-84944235051362011209466756532688449626279114121412608 + d *
    (58629598870231865985103594468682745961891285850914816 + d *
    (70527379202750600196470489395342112808329159274659840 + d *
    (-314942724981736632782896502699237068096010258339332096 + d *
    (602994075581056235520271389458732129337256698592886784 + d *
    (-756545136030015234652190739241940599212187460269244416 + d *
    (529698188511403415904449816250772398195640688177053696 + d *
    (279526940739656251603790910767387887266970074235535360 + d *
    (-1673356085833150184338998606147722414225941679350743040 + d *
    (3324059195813775126296666573432462175715603805048143872 + d *
    (-4558223354211593222016685484374598086306364796567027712 + d *
    (4515415431689722996475874389357306406617099573303705600))))))))))) + d ^ 12 *
    (-2467614442034586636308920310094511528160953299737772032 + d *
    (-1799491504539390112428029336412526727304043520263979008 + d *
    (7700462349121856671430327600675703948269077459264864256 + d *
    (-13812405500738891787708827808745254938648475267087466496 + d *
    (18159738458079113319266964771399526883276342249253765120 + d *
    (-18770176249519122055052443144991791406477099373956956160 + d *
    (14333181166473719954253121560898727482086893979051753472 + d *
    (-4733290276422357945403723658888000565145515524515430400 + d *
    (-8740789304884248792568285182684657162393087991187243008 + d *
    (23602591991352584592004603432276895522700904444953886720 + d *
    (-36738060468606702825189215766355013041225416564321288192 + d *
    (45166689366455019718493943624083319234614108636027289600))))))))))) + d ^ 12 *
    (-46765343137784859966989235634132620120151827695323578368 + d *
    (40751451847151816321202994838038099288585026792540864512 + d *
    (-27811277933068328859615682919172923229195306366455513088 + d *
    (9873304684408810342730869013582094907156979847044530176 + d *
    (10375161277937184063947109915435443701413200875181047808 + d *
    (-30076543453922450194651845919884243336759011001138413568 + d *
    (46743914637790890365227458696235506338899735281909891072 + d *
    (-58642116175024840289565979987232082687945672431226060800 + d *
    (64958022319986910697595624119734523665386221113638125568 + d *
    (-65768462933163556235625852615223357218589619188397506560 + d *
    (61856958745442274474119726674532922635182200175475818496 + d *
    (-54449950673069784497454102429203693493486320084332838912))))))))))) + d ^ 12 *
    (44941449563333781205896424809311616902021387686103744512 + d *
    (-34658745303953762568005742361763832035377884054261334016 + d *
    (24699169333655375569175599662194918680296130470066257920 + d *
    (-15845877673782854543856460585648173791097652360378580992 + d *
    (8553735227217828429312458505310240967192738307953655808 + d *
    (-2986534358165247979064236573865328724531125173617688576 + d *
    (-916291046879122139807084148260293509846256942773436416 + d *
    (3363229062100684767819671919062537490673707022874312704 + d *
    (-4639277794158006533395621319671426807940879240118665216 + d *
    (5048363544515634160261600643615514331107968907939151872 + d *
    (-4873038514061926667822903076542550986471427931878719488 + d *
    (4350949850930131940497402596120450248104464084797489152))))))))))) + d ^ 12 *
    (-3665212466478736087370531315212452381253029814379479040 + d *
    (2944846482333706500915505331444480086334547406289371136 + d *
    (-2271458958476526439828305813484809737449305220872929280 + d *
    (1688944694959168932053280800956131097672114501428445184 + d *
    (-1213816279810676559103589590531502854329366584297783296 + d *
    (844620706398385706146490038626024775830345901722042368 + d *
    (-569628379287177230079953963117454826271379815752269824 + d *
    (372533104810140269327323194327949379611315988570046464 + d *
    (-236270381533242119627061122781075534866950461372235776 + d *
    (145266903164890606910794943417271194093859016834547712 + d *
    (-86512433673632928735055661246230050149809828247371776 + d *
    (49836165390919924569143159789216286670706179580624896))))))))))) + d ^ 12 *
    (-27710391082275042768789150705697223747478988499976192 + d *
    (14824569114358761306184533427040397193786158236565504 + d *
    (-7593350909210146607242103439561350041733238510583808 + d *
    (3694843429518413585976708660873510504000265419751424 + d *
    (-1685155735658724995190461001755864038286187311923200 + d *
    (702074223697892814176684419698634611649274229555200 + d *
    (-251710797812941728439607348420475045430105879871488 + d *
    (63320344116791300072407584553645510089522224037888 + d *
    (4546680329874739927929354258661863799151710961664 + d *
    (-21817885756575113992248772043198671748205172228096 + d *
    (20793140039556354502508267316490626486739483754496 + d *
    (-15073242855348458386365767692757662141423177170944))))))))))) + d ^ 12 *
    (9589686391613873355154070548858307207801484869632 + d *
    (-5614512067210416351887744507753227256225961082880 + d *
    (3090827042250739979484149900321718189570382364672 + d *
    (-1618330826284329678932726243493444464891826798592 + d *
    (811321316291966052330507273929033247150057979904 + d *
    (-391049645733859600488684767807951336441875529728 + d *
    (181673681599725532056687834722716699969984659456 + d *
    (-81478455540695804349251114395524449268156858368 + d *
    (35305828095958222971620170476514264946232524800 + d *
    (-14785410895830993569495051950326193219713630208 + d *
    (5983379539309745837260774907585131451875590144 + d *
    (-2338649573336668990144931354121247621418319872))))))))))) + d ^ 12 *
    (882097359925060307214188275444418094878949376 + d *
    (-320684809944543334876921542444971170675818496 + d *
    (112194861101822950947684750653211915188699136 + d *
    (-37700886881324192251599260906831028241301504 + d *
    (12138572430955804465384592139313909834448896 + d *
    (-3733673178428474854642250702219932809035776 + d *
    (1093150414471818370635011898118577413685248 + d *
    (-303289257746780494837929635728015072428032 + d *
    (79299227742112071551616826729106384879616 + d * (-19405623248592179000168586913472228884480
    + d * (4406056226368943707582945117447303200768 + d *
    (-917721820866790957249572146604118376448))))))))))) + d ^ 12 *
    (172664852356406643908488231662247739392 + d * (-28690545056092608468598273670661799936 + d
    * (4058530652241770100728436267109842944 + d * (-454766903625474040921197745185488896 + d *
    (32817615979990352302904062430412800 + d * (241208812190073373333104681811968 + d *
    (-462198542954406182883547579416576 + d * (64194881799170521212626847924224 + d *
    (-3753965199526721737355602690048 + d * (288022155058375348962539339776 + d *
    (-188262155985804607096552947712 + d * (58561148732852814699483365376))))))))))) + d ^ 12 *
    (-9459820172840771174635143168 + d * (695956637440664723534643200 + d *
    (37975566903673868049186816 + d * (-14765453537214149746491392 + d *
    (1363118492520756699987968 + d * (-9596087243328385974272 + d * (-6851094917468558983168 + d
    * (195394874567321976832 + d * (11909246845656498176 + d * (4701521148139798528 + d *
    (-317947642489864192 + d * (-55932396562284544))))))))))) + d ^ 12 * (1594658625945600 + d *
    (345004530466816 + d * (16128676200448 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt12 (d : ℚ) : ℚ :=
  258194943347600078171571735737640419328 + d * (-11419194580111680484144776849219045556224 + d
    * (-11237004271770987101342828717436945039360 + d *
    (78268083983320959691977615414615903043584 + d *
    (-114219683639021675267333197383250237980672 + d *
    (-34575187124395669274907335923527173799936 + d *
    (606454909965227005071344378088839269318656 + d *
    (-1440373644442049568044178970674803568844800 + d *
    (1479662680751110104289955694167707284753600 + d *
    (894668221530913719852559086862802451100813 + d *
    (-6558320820497732409884071262404088068307038 + d *
    (13493116453642040907702693642010603041861653))))))))))) + d ^ 12 *
    (-15149871848051660499140867802438136538623337 + d *
    (2185332633460264944482927890153545294172546 + d *
    (31391241956758490508796669036059665474146203 + d *
    (-79871020150832408050348210683848739119273742 + d *
    (119926262281063500738168628542311397020447470 + d *
    (-113416112142722061509406403237522762902144080 + d *
    (22679744633535737814285672177247172380552528 + d *
    (165320605669489114667204419422013625318966196 + d *
    (-416538637142961904107401648996423936343316120 + d *
    (642456146676576354339149817975597791965372273 + d *
    (-718153306541177460447998479369170752647272796 + d *
    (525758768324667695699978582511263036265296696))))))))))) + d ^ 12 *
    (-9652445062437534556516640980759143155323343 + d *
    (-778895011436288331082885818410522443958721694 + d *
    (1669483241620778434227609503619666552374388813 + d *
    (-2404256172097993090855466214391033715644735990 + d *
    (2707813354821559278704746296400218376797002787 + d *
    (-2373444155035559160046282491463894197904285137 + d *
    (1336247424646086968303361530734601199068803207 + d *
    (292378042291440422843480626140483622769719448 + d *
    (-2240978431255511266094221167109770172875372065 + d *
    (4139631080723928275405412425292730204439325269 + d *
    (-5607037369703209888856126201421492748280190764 + d *
    (6337076100782290385877394323182003450013832449))))))))))) + d ^ 12 *
    (-6161709135432719672526856402960542883035975680 + d *
    (5076760372305007718576909038688196244735662717 + d *
    (-3229194670341492396929203917609798480598436592 + d *
    (874757138615014394654258421439145797271465665 + d *
    (1679544527042551723224388153067670150445438414 + d *
    (-4133075153601850593016441419541217327028152289 + d *
    (6237602613491758365445588333464947257471246735 + d *
    (-7825280488816315368695092974638430321292735839 + d *
    (8817483586334421682956900920696628249514669809 + d *
    (-9217491384457729914519059300113301710039651077 + d *
    (9092318320171067798774293477109881057338656237 + d *
    (-8549562001734622184847374961311116586692598353))))))))))) + d ^ 12 *
    (7714388942589295288462442614142442028227189151 + d *
    (-6710263816143773640345055237404630023015122853 + d *
    (5645299744560366946509107305491140267166838646 + d *
    (-4604577370844301192771015449650641241811801523 + d *
    (3647686545593644392949907212007227914016519703 + d *
    (-2810155321787929010661325124476783854171851560 + d *
    (2107283894999888212807920950547835448603917943 + d *
    (-1539060265151127549518610974256527301249722660 + d *
    (1095151663460350430111267730037115087329348905 + d *
    (-759321418927253085171272524394976912069804414 + d *
    (512938342230729774652344408550440094257586579 + d *
    (-337488779413215567262277689934501606513554215))))))))))) + d ^ 12 *
    (216163288230183122207625100434068777489664068 + d *
    (-134679748377102014809797189293776681712381235 + d *
    (81538588136084232493547003622939280406732964 + d *
    (-47900860315794589220762901807097796920882443 + d *
    (27251812049551479777420062768619403504811694 + d *
    (-14974165679373147760179443402874054681869549 + d *
    (7915881373772846515260161186083130281854793 + d *
    (-4002580490134100100737802872506558820027375 + d *
    (1917958506177081830010148750165831083433625 + d *
    (-857005145329927071786130766722178760435530 + d *
    (345780328712686817751923717045885301218777 + d *
    (-116219493497318506176477605699174599055012))))))))))) + d ^ 12 *
    (23136504651569446576065467902819073817806 + d * (8373278189111192639530976040752953704451 +
    d * (-14805810755801824752089148120009392024215 + d *
    (12699911342000861018550612211220487644086 + d * (-8817131159951725395510761149021487212110
    + d * (5469907657628993078665163703482367349777 + d *
    (-3146032575843486974763012650304990248388 + d * (1707413172940850000323109012183419121422 +
    d * (-882874829631304637395155008763314967536 + d * (437439476628157223281080809124328496531
    + d * (-208402640304317124504701265887327679783 + d *
    (95667587367820806569543146323594689933))))))))))) + d ^ 12 *
    (-42365159758420634410116878366692816316 + d * (18107008414049058472942389454170832918 + d *
    (-7468926231951913744744172315334732730 + d * (2971839743331396922305203407459988496 + d *
    (-1139582857288841986394134676086070162 + d * (420562770200051296851049933601853841 + d *
    (-149105453925936361834789636950627124 + d * (50667704158696432598054664109518252 + d *
    (-16454822450837081814775673799160009 + d * (5088870709816877550634276327159336 + d *
    (-1491927523422298208598562091181773 + d * (412231594821047293790838191272127))))))))))) + d
    ^ 12 * (-106540050794368376452326318989998 + d * (25502568443333733895655046004083 + d *
    (-5582092043242435787441292294238 + d * (1098682739639821623287150123798 + d *
    (-190092303090193589937685341610 + d * (27978817597663532487613468043 + d *
    (-3321382411224326794222489890 + d * (286302882649925204240527124 + d *
    (-13250987915157497605510465 + d * (-137410519399121633725121 + d *
    (-28880346587133593494875 + d * (20118394838384704171401))))))))))) + d ^ 12 *
    (993057550822434201835 + d * (-1640580567631844771702 + d * (407993703258712139934 + d *
    (-52344364031754454513 + d * (2997877269556853334 + d * (124741181593659906 + d *
    (-31105025287406876 + d * (1235297550644768 + d * (15119808092600 + d * (10683300352341 + d
    * (-623811388593 + d * (-175034210043))))))))))) + d ^ 12 * (5024074303 + d * (1234117412 +
    d * (58451797 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_12 (d : ℚ) :
    orderSevenSelectionPolynomial d 12 = selectionExpandedAt12 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 12 =
      selectionNumeratorAt12 d := by
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
      selectionNumeratorAt12
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 12 =
      selectionDenominatorAt12 d := by
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
      selectionDenominatorAt12
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt12 selectionDenominatorAt12 selectionExpandedAt12
  ring

private theorem selection_cofactor_eval_at_12 (d : ℚ) :
    (selectionCofactor d).eval 12 = selectionCofactorAt12 d := by
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
    selectionCofactorAt12
  simp
  ring

private theorem selection_factor_at_12 (d : ℚ) :
    selectionExpandedAt12 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 12 *
        selectionCofactorAt12 d := by
  unfold selectionExpandedAt12 orderSevenDualKernelPolynomial selectionCofactorAt12
  ring

theorem selectionEvalAt12 (d : ℚ) :
    Internal.SelectionEvalCertificate d 12 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_12, selection_cofactor_eval_at_12,
    selection_factor_at_12]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 12 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt12 d
#print axioms solution
