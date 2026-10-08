-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_36
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:16:14.985123+00:00
-- url     : https://prove2.me/submissions/fc6daec8-e402-49cd-b532-18fdb5d1a097

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval7.At36. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 36

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt36 (d : ℚ) : ℚ :=
  -8417477703957894660096 + d * (-658558904183783424000 + d * (660894058188023205888 + d *
    (-1481248194241552616512 + d * (2975908218529694891904 + d * (-2001366581707064578560 + d *
    (421578171327450225216 + d * (207982380848422816896 + d * (-388342256998603512576 + d *
    (504897095017329073216 + d * (-376802223687693780672 + d * (202103632043250499008)))))))))))
    + d ^ 12 * (-100617074648002428224 + d * (39124352216405024448 + d * (3958091647235109888 +
    d * (-20706979252028131392 + d * (20168109559167618432 + d * (-15428824413039673152 + d *
    (10490697602503323520 + d * (-6224173781588647296 + d * (3327013104045172032 + d *
    (-1708513249949736384 + d * (828899406803353344 + d * (-357359285155716096))))))))))) + d ^
    12 * (138091303269032256 + d * (-52502430837956544 + d * (20089351718110848 + d *
    (-6797581893762752 + d * (1816492514413824 + d * (-423999424694592 + d * (129315752385984 +
    d * (-47659300868352 + d * (13079685628032 + d * (-2119986999552 + d * (285123421824 + d *
    (-115157248512))))))))))) + d ^ 12 * (43681808640 + d * (-7302111936 + d * (274402368 + d *
    (-25081792 + d * (51550272 + d * (-10553280 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt36 (d : ℚ) : ℚ :=
  -9976112671590501580800 + d * (-819442787039071764480 + d * (1084185231320387616768 + d *
    (-2487883003300848734208 + d * (4653604765728483661824 + d * (-3631848397273934425088 + d *
    (1551509002701059641344 + d * (-593160451648052682752 + d * (184450519210390918656 + d *
    (264093504757897789696 + d * (-375799078580459009152 + d * (280775439678157596992)))))))))))
    + d ^ 12 * (-184217596546041733248 + d * (107983547342305145216 + d * (-41151014699861385472
    + d * (5375122661822974784 + d * (3870442295487459776 + d * (-4459391279144526656 + d *
    (3621171895389821248 + d * (-2323666718313185856 + d * (1250737029146855936 + d *
    (-685513649128526016 + d * (382971931562823296 + d * (-189827092290334336))))))))))) + d ^
    12 * (84158401990630336 + d * (-38523826425564096 + d * (18500075146446976 + d *
    (-8264370013005440 + d * (3346251910102720 + d * (-1325260905259072 + d * (523238966110656 +
    d * (-190614709769280 + d * (61926063720000 + d * (-19071310250368 + d * (5845884854144 + d
    * (-1623813277696))))))))))) + d ^ 12 * (346166873600 + d * (-46219659776 + d * (1962292224
    + d * (410851328 + d * (-50004992 + d * (-1324032 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt36 (d : ℚ) : ℚ :=
  123143668543102132943218712567611289388739711738969813796662542336 + d *
    (-5746458149277088360077653991057549967748933164451139429490816450560 + d *
    (3798304195336777788367262008627929692641361647079090880347281293312 + d *
    (3670815563580537672766826591356736274663617254555813403871009570816 + d *
    (-5975007241325464787987853224960958920573908537505799546294918709248 + d *
    (10481850092695044165036244434499341491568207158259809095747048046592 + d *
    (-9276600539404387244753654639776211998358278934719417710883475816448 + d *
    (755997288342320788168564071953318248752653793027341375270912262144 + d *
    (6650912746889010168360262912172937325986091741045868942799264546816 + d *
    (-10401874195469954036963101660358841749645401830453932421838037319680 + d *
    (10628168105838019077050212944426364581394148418871762634115281321984 + d *
    (-6471249152670918822375776509225845643146547900877711348374112305152))))))))))) + d ^ 12 *
    (313759022636533474365850037223845344845413876573918694902080208896 + d *
    (4273219599386287656078108497391289654926640614744521551391273254912 + d *
    (-6285860779997585081619753820070369935675188438887747276076823871488 + d *
    (5896102941173554101369704633228684251266146869336236127179989319680 + d *
    (-3671319931958323068486191970322091188825941160120940827048582840320 + d *
    (893962207650331184770077668837776876981357844453611342893720535040 + d *
    (1279016990497091081043021485070012302411053097089281766520824791040 + d *
    (-2433993040924391535185421662221331057376194459572720137400119721984 + d *
    (2613702388013749866980883134475278280084035972257076577156491902976 + d *
    (-2087738169356094085184013663526196061549424297010154407087408676864 + d *
    (1263358936615570206974475470871258251847833827901422912979491880960 + d *
    (-486358858212347795047887462802691561627289663543084684352073236480))))))))))) + d ^ 12 *
    (-70120787046600663080436432220931179909089170577535282581517107200 + d *
    (367001721043828132655962998266758538838554490529380785341432856576 + d *
    (-445448199329271749925535383680882472387496129540830487573898199040 + d *
    (387441990256410416264759877903947595157021701723846613462230237184 + d *
    (-273371775984619048166615390301991332955306212828569320896577142784 + d *
    (157495116681770943713641184408093836532066338619620892307043385344 + d *
    (-67225072528401356808346152854196240534244459515194814414940798976 + d *
    (10221448774295179627675273109130378330701938845935320065531445248 + d *
    (18045123339133695400868731096942250390281790976955332457126166528 + d *
    (-26811258823540854152694979108181141299090386144323629748320206848 + d *
    (24877141358398770186624841362374182227700626493328584149810806784 + d *
    (-18655339002838987846226432788486101595870618804722360241590632448))))))))))) + d ^ 12 *
    (11989299670180972832801642117563018532847019243735704287159517184 + d *
    (-6636452329745087892650145131930125219595215695320197698599256064 + d *
    (3018690244450662874060106966027617432719733824838245189001150464 + d *
    (-911055149910036701549497177360779032731889047187061535145459712 + d *
    (-120447598178157235930979021790621363907588344185421291807834112 + d *
    (496662425685960927041651070034694598436558909471091584362086400 + d *
    (-534152749988212983508965072949369164923232298536189808759799808 + d *
    (432802795103034709999831193802694503884123211653974388426407936 + d *
    (-300870298687701503136593792529030070016122323407183010543697920 + d *
    (186675144737199968709191096604884810444018933027309422335492096 + d *
    (-104406438033029710329075777646547843458062747825611605974188032 + d *
    (52055495258149063343126929474271941051705443396764730407256064))))))))))) + d ^ 12 *
    (-22118745086218531030550833376763243295427436665016150036316160 + d *
    (6821459798692916731659444565064613931314987044710283664424960 + d *
    (-67268890111863339445177374045608080960193844363628061917184 + d *
    (-2230985887682765443036468308131987049559493918562760032256000 + d *
    (2500593770744264564541713410409771374076897829032095004753920 + d *
    (-2030568343921446683593139704070236118067740705481856193134592 + d *
    (1423086089055891471906004453112323547037538854170210258386944 + d *
    (-908905976251934836897876978647465192954190972073129205825536 + d *
    (541643545048767419854693606455624379799356710525831742750720 + d *
    (-304660918820079607878513999085411865904840176465337673580544 + d *
    (162631072576498527754221257008004374343011942282008916656128 + d *
    (-82505918141056644301000014399732715662683489005051135655936))))))))))) + d ^ 12 *
    (39681603215038854295839141001302175521379438399490388656128 + d *
    (-17958827779346508304378239045115632066405067253513665380352 + d *
    (7526801848724838083317896036041044600492369394846071259136 + d *
    (-2819781227623586853310448058326348391266221399686113394688 + d *
    (857054105915278153423513946418583501984950691699499466752 + d *
    (-128532017220717271253695281359608673152176553315986571264 + d *
    (-88161060460338867686751157947211112330928665599339397120 + d *
    (116817293700712239926926322141643733341097811378568691712 + d *
    (-90907986765770485036747651306451668194350327931794620416 + d *
    (58898478493765272093562910027389631162598764587707531264 + d *
    (-34462400308540929425454984807449971597415458966301048832 + d *
    (18804945930264641655606617345131024971802314921394831360))))))))))) + d ^ 12 *
    (-9722418371355115225515301861754317985807319038682464256 + d *
    (4804922633210513663420768427450445365509023803822833664 + d *
    (-2281777894982838323517251540110832385376283932078112768 + d *
    (1044497768471575958213935851243863290736551465213755392 + d *
    (-461743456001538679113543381547105687647935498002366464 + d *
    (197308536994828394792927417141588380073911935508938752 + d *
    (-81500929083050065290485029113353361937166275767697408 + d *
    (32517077528223335994067851715274720510301802512777216 + d *
    (-12510397222274109659403650087277921092389732845355008 + d *
    (4628214869282192335198697614211710373620694000599040 + d *
    (-1638727213632519717291376330287671518149192375336960 + d *
    (550973126920863077233951437045496326202790955188224))))))))))) + d ^ 12 *
    (-173480278598713180145996428574781544367542933127168 + d *
    (49782545317042029132675351781667171381648777543680 + d *
    (-12207633296285449575636593199665056841554990465024 + d *
    (2027815440440379046799574884733083835243538153472 + d *
    (185100840593395321134829315589249966115729440768 + d *
    (-398967428391485408620270970839160065179948679168 + d *
    (256995528987038329940479361255619338256991125504 + d *
    (-128619482057174521258705844217894909769693528064 + d *
    (56864500858641659657507419406506061625300090880 + d *
    (-23205810188074228975537564617954149683647741952 + d *
    (8918492708974458689770543603026308942977302528 + d *
    (-3262561695862851017997902104704295246838104064))))))))))) + d ^ 12 *
    (1143014497364096876838551053168117338952695808 + d *
    (-384828652507301569820308764625837963119689728 + d *
    (124716299923141353078332373717562540848316416 + d *
    (-38922598866314450938307890489969736636432384 + d *
    (11693422545775957068140020237557529643843584 + d *
    (-3378537367576901616871231423332478222336000 + d *
    (937233618466125618716407995855747912564736 + d *
    (-248965069216403121715601024971135458738176 + d *
    (63075266843057568376353109277544687599616 + d * (-15156760306984407821709303789133000867840
    + d * (3429171927650978463936419237061092966400 + d *
    (-723197117105439050600759169564791537664))))))))))) + d ^ 12 *
    (140107277890603024599191599025335828480 + d * (-24370445904770886302357184643895394304 + d
    * (3661101813100571963674650156252790784 + d * (-439870587553520387692040243580239872 + d *
    (33799251368778061733939857731878912 + d * (555585153842454935852945725980672 + d *
    (-660727592082953199621661783228416 + d * (105006929030070791754718480695296 + d *
    (-7290337149327238587287994105856 + d * (43007179420450081317880594432 + d *
    (-78221605134671378267511980032 + d * (45797275451428322872450351104))))))))))) + d ^ 12 *
    (-9202182952384067594454564864 + d * (787435009728267425793179648 + d *
    (30667083653292682856890368 + d * (-15027343515615712544030720 + d *
    (1375502236774587641888768 + d * (-2779715910577397694464 + d * (-6909833414558590173184 + d
    * (113693337837840891904 + d * (11447034516096155648 + d * (5163630731510677504 + d *
    (-288720917533032448 + d * (-54826344403959808))))))))))) + d ^ 12 * (1626305127776256 + d *
    (345348295622656 + d * (16128802029568 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt36 (d : ℚ) : ℚ :=
  1361654474984428587559608150456969957213435663268970496 + d *
    (-63426709308336305014807577209793947691301052241915412480 + d *
    (36442774169567225461923157008762358801104936205188857856 + d *
    (54352396507562617730715034446473691743642574061572194304 + d *
    (-75626858746566134327733331529034569693462487157344043008 + d *
    (107042081911212308077689854458239094437632710443493490688 + d *
    (-73426508544603675847628256480280893994524392313559449600 + d *
    (-29033568409737782568701013359637428696054340027925880832 + d *
    (98631468600262242150097115272347801348881473573438619712 + d *
    (-111623018309069450050727132688985561288600431227059689083 + d *
    (85695253104807657918206445182307989051559515441038107890 + d *
    (-27925240794612868958394937689699589903199907673663455571))))))))))) + d ^ 12 *
    (-31495598000481656041131607265171346023268290324644421585 + d *
    (60770384355608415595815648110421345862078572304788193114 + d *
    (-60360127687481474175904833358731332452961545687516716837 + d *
    (41890393332965552016729585839154140526290283010427097666 + d *
    (-15272048443679687355150058018987968316288494638225680322 + d *
    (-8158053614949411982366611818328801119862562057549912520 + d *
    (21188412878429638808435938196231312470398895852630154728 + d *
    (-24094560818331790151532623756249750990863916732033564508 + d *
    (20144880552186786573109847429665341078258288287347965632 + d *
    (-12826532030938125702721652048858637774151072687286639471 + d *
    (5446398599047668047290297835357311063389222645171232460 + d *
    (-69176142703537521186122929968812668532852417480029480))))))))))) + d ^ 12 *
    (-2861444489138993222999014360289705242433836518709682447 + d *
    (3783556882180343493240694604680771852352349780036508730 + d *
    (-3409377016890633388413573416218841754307197772797738243 + d *
    (2461577724863978163771946579486456006165070805020118146 + d *
    (-1465957940327563935249396574598615208238552752959502933 + d *
    (679362267366505125005796546431586488067741436360132527 + d *
    (-168634521802123260118872827241936702413718365057020865 + d *
    (-97932760892510708181701027649597677710695762279858184 + d *
    (193728651855384410143092978887816421609711034140581311 + d *
    (-193603719581279556361556673558719731375412342304909907 + d *
    (152334376149276080027105820046520010504583687943130076 + d *
    (-102556637249654807969979766788795854636247077427949839))))))))))) + d ^ 12 *
    (60220093459302627418968132256529536005356338111740136 + d *
    (-30308074404647863529242030815939545714185632700034355 + d *
    (11941160708637938904826098739341274473181048043598408 + d *
    (-2161028214086723229062557895765455862183933740397495 + d *
    (-2101509403638254287951574473319501454955417203996722 + d *
    (3287801544866806179070362498740779503848154830029599 + d *
    (-3038406618134646538853168867670092128732223950255409 + d *
    (2299249692126850171805717834989692589680169871157393 + d *
    (-1536260522667239915745647136253164605372312324223351 + d *
    (930507273160607998323721735603899298033897261727451 + d *
    (-514306524303253328414325654665977919452568432407459 + d *
    (256902332758258031183915670955515277011568235073047))))))))))) + d ^ 12 *
    (-111858941396063551295091600285640473242909044613153 + d *
    (37796336233957153054521438325709127409688831338435 + d *
    (-4430825746555952073798764864812180136210027240914 + d *
    (-7774045736433734144113950196679586888644394413283 + d *
    (10179547672283908701200668110102394539377311624511 + d *
    (-8786627561149544176927456652945797228826337466624 + d *
    (6442079610823981157888121641431748785220276600015 + d *
    (-4298280040947198395923697075369191013703127624796 + d *
    (2686987815168085636471979974401895232422694135721 + d *
    (-1597577248964538827257476287758447638127777735014 + d *
    (911410617504139404756279575587069706396940072763 + d *
    (-501711001259077346416065213262596428907574251735))))))))))) + d ^ 12 *
    (267458039797988865552615758522547551772109647908 + d *
    (-138404962177642956272307286283818399971488552451 + d *
    (69637748961247988559129224160364922780970975156 + d *
    (-34104504657264657309787726247922026273091833331 + d *
    (16267866555769449881131384388190946773224428326 + d *
    (-7559842318342535472221884243438730815773652733 + d *
    (3422544971558081835068959960571902958239307137 + d *
    (-1509110278814922352501619415584092432125475727 + d *
    (647700666626224813050118042141810097878876985 + d *
    (-270338392475350717445840870699769014505061706 + d *
    (109589604562737808722739532627890303656605705 + d *
    (-43072505255919862110715521080441347681324628))))))))))) + d ^ 12 *
    (16371601973020433953974978679803188779646390 + d *
    (-5995008658395742760390194873008412058244725 + d *
    (2102951329403562114954792192119959916249513 + d *
    (-700408107183263268249036832428767798105858 + d *
    (218101986351531511428049143509008530782082 + d *
    (-61568513565990224589347775641819132296367 + d * (14594140946163901108681220643489057446220
    + d * (-2129488764467030125295333673708618556634 + d *
    (-439495287346289089087300797344133388520 + d * (595900031884569373573799432668608480467 + d
    * (-363836169546355703857329055222925089791 + d *
    (178576808328176839618256085803572097981))))))))))) + d ^ 12 *
    (-78239227228981170059097745034089546772 + d * (31788751962562557478019325158211287542 + d *
    (-12193565689407647221367520770516545954 + d * (4457516623086271668687493596815962872 + d *
    (-1561222320301526510473866259437995618 + d * (525550832963803663627802424109348105 + d *
    (-170350269075084901060510884593130988 + d * (53199137582499006608789061383003484 + d *
    (-15992021004589030566476071720152697 + d * (4616834513036373031980966298095616 + d *
    (-1276331881491664801312626115090253 + d * (336947913185302083363646185776495))))))))))) + d
    ^ 12 * (-84693747680271155956624390256038 + d * (20161146728309299113660623988891 + d *
    (-4495807079206478901422843558806 + d * (921202619607854824902176318870 + d *
    (-168424257909980054968375867426 + d * (26326729178958285117640800539 + d *
    (-3283334520072026247102249282 + d * (280391066843214020878391204 + d *
    (-7201063763249508991774489 + d * (-1847829904999785692023721 + d *
    (216937883759729374095045 + d * (6101839639800672675633))))))))))) + d ^ 12 *
    (-457714747320112442117 + d * (-1300108637705516590310 + d * (388422056786239316430 + d *
    (-53119845341972811649 + d * (3048424346344419294 + d * (138007304206727202 + d *
    (-30947821021337972 + d * (1020966245516000 + d * (12809467725896 + d * (12129538711869 + d
    * (-527319958857 + d * (-171405697995))))))))))) + d ^ 12 * (5130801775 + d * (1235336612 +
    d * (58452445 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_36 (d : ℚ) :
    orderSevenSelectionPolynomial d 36 = selectionExpandedAt36 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 36 =
      selectionNumeratorAt36 d := by
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
      selectionNumeratorAt36
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 36 =
      selectionDenominatorAt36 d := by
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
      selectionDenominatorAt36
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt36 selectionDenominatorAt36 selectionExpandedAt36
  ring

private theorem selection_cofactor_eval_at_36 (d : ℚ) :
    (selectionCofactor d).eval 36 = selectionCofactorAt36 d := by
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
    selectionCofactorAt36
  simp
  ring

private theorem selection_factor_at_36 (d : ℚ) :
    selectionExpandedAt36 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 36 *
        selectionCofactorAt36 d := by
  unfold selectionExpandedAt36 orderSevenDualKernelPolynomial selectionCofactorAt36
  ring

theorem selectionEvalAt36 (d : ℚ) :
    Internal.SelectionEvalCertificate d 36 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_36, selection_cofactor_eval_at_36,
    selection_factor_at_36]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 36 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt36 d
#print axioms solution
