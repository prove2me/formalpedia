-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_23
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:50:13.376784+00:00
-- url     : https://prove2.me/submissions/949dad41-b994-4857-9f5c-f9d2d37c8b21

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval4.At23. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 23

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt23 (d : ℚ) : ℚ :=
  -39538903224435776000 + d * (-5637876485910547200 + d * (10635369781114888320 + d *
    (-23413655583055137344 + d * (36578997701847019776 + d * (-23407493918973386880 + d *
    (-321829594238709312 + d * (15173563174369803840 + d * (-22000893423892326720 + d *
    (22922689172062813888 + d * (-16548115369107352128 + d * (8236808425940484096))))))))))) + d
    ^ 12 * (-1875741094038860224 + d * (-2425322681470636224 + d * (4882635369190498176 + d *
    (-5441270581313382912 + d * (4771224212912651904 + d * (-3677846565700083072 + d *
    (2564516250892637824 + d * (-1623533244684573504 + d * (949880473687080192 + d *
    (-523172486283835776 + d * (268498983017726400 + d * (-125760339018949056))))))))))) + d ^
    12 * (54217272413503680 + d * (-22245550446602304 + d * (8658039570007104 + d *
    (-2998900107011264 + d * (882197011665216 + d * (-241974345232704 + d * (77692479649728 + d
    * (-27391608876480 + d * (7715691889344 + d * (-1470307280448 + d * (256972827456 + d *
    (-91586020416))))))))))) + d ^ 12 * (32478240576 + d * (-5909598528 + d * (358477632 + d *
    (-53027008 + d * (49693248 + d * (-10583232 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt23 (d : ℚ) : ℚ :=
  -46859133461932408896 + d * (-7136961456777573696 + d * (16292004829145374976 + d *
    (-37510296861976496640 + d * (60559080770617006656 + d * (-50071852931566761536 + d *
    (21438613550893952128 + d * (-1209056424660421760 + d * (-11699488737275665792 + d *
    (21452491337867197888 + d * (-22091926479470184832 + d * (16679780740005208320))))))))))) +
    d ^ 12 * (-10524381000192003648 + d * (4983966834010972864 + d * (-632388007293745024 + d *
    (-1570389614490925440 + d * (2009083651070082112 + d * (-1709683064472699520 + d *
    (1236032854288025984 + d * (-792830765895277824 + d * (474829733865844224 + d *
    (-280927789333887104 + d * (162498719620963328 + d * (-88724585247991296))))))))))) + d ^ 12
    * (46314413002781760 + d * (-23899158204525376 + d * (12079458671005184 + d *
    (-5797806297906944 + d * (2634025641633472 + d * (-1145889584886464 + d * (472212166250880 +
    d * (-180060705811328 + d * (63503547031872 + d * (-21071254185344 + d * (6478022393216 + d
    * (-1711701058560))))))))))) + d ^ 12 * (346959809536 + d * (-45315987968 + d * (1982619648
    + d * (392773632 + d * (-51828736 + d * (-1337344 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt23 (d : ℚ) : ℚ :=
  12749380188038893913848396175852712611690710858569972187136 + d *
    (-589627252214718339974538477828645731701894393965610388160512 + d *
    (232172662251062706592836455357044862053430307389527673536512 + d *
    (978044710661473440445770954328018197174282226047043234168832 + d *
    (-1878910530877759280897155405220574019654423059027049308225536 + d *
    (2663584943375840423934010293165040297124638684439094720462848 + d *
    (-1214295899489384996877007061065022648673321974752830828576768 + d *
    (-2891387215816117633742758560177710105017169536129447265042432 + d *
    (7058030939093445291269723286801822247530498793090717239214080 + d *
    (-8828093071541100427120163496876691315385050649338581789179904 + d *
    (6372733064188456108146496434302535337860202397424735527370752 + d *
    (804886172596940828559173386672203518837586487706383846998016))))))))))) + d ^ 12 *
    (-9897226421261873025292241591876546032458243298389927648559104 + d *
    (16326508243843025976417622915750700985409506418299049742172160 + d *
    (-16737906436794673212392516432166009241844816140932100106223616 + d *
    (10077499348642586532020223743721458569486331097694057685581824 + d *
    (1816245574179965835790212374210379130813089430487538356715520 + d *
    (-14560208151165419386733062298978523823217495464852670247600128 + d *
    (23394935799906390323207029561546841274721905575400021956755456 + d *
    (-25297639948749819573312609605294836747037317921988870920994816 + d *
    (19827910681156108973407661743202997660554927563584521762242560 + d *
    (-9068528184803563234713346069223833375461046974521728959250432 + d *
    (-3313716891955031391908721245967078605107982587684782280540160 + d *
    (13620811269743551969647560793759658162257517710538829545078784))))))))))) + d ^ 12 *
    (-19383207413588856467451937460705669148713600020182584035115008 + d *
    (19871784264493182241509421865254518948493413934120454634078208 + d *
    (-15967160585343145690517564717606029445945868379932304790519808 + d *
    (9554473997180221627229829689308513316603801870427609706790912 + d *
    (-2720142095100080143749896492830260116450535811558772001996800 + d *
    (-2892653120440296628305932214965171400345772807268957097295872 + d *
    (6397302958849581642525335294080982317839719281217301645099008 + d *
    (-7670809283370780278235783397010872780024525165600622943404032 + d *
    (7147724115165906824278051612955750115312910692177631942541312 + d *
    (-5525076555419981317951973690652643267827571875352421674516480 + d *
    (3500146040670113298533235969780740048926174536948153200148480 + d *
    (-1605971649269286693054247676051831270612725989152775617380352))))))))))) + d ^ 12 *
    (149935167385433231315617192359705992331374861952698414530560 + d *
    (768708266130540431621265432144436275114354665966742902145024 + d *
    (-1197581792610671266694260801517355298877670743002193194385408 + d *
    (1260474232454307886085702157525267689133062386965030440271872 + d *
    (-1099372781732815822655986782694438981336141810135798888529920 + d *
    (837535370889557931094547795278926229798233687799616833847296 + d *
    (-562881007690349244838439582240651193387358847342257459429376 + d *
    (326459829506463016526849698957582476794743573078818951528448 + d *
    (-149386045499833928235236851186778897477607287364686792097792 + d *
    (32667437101131375421958972971118682608984268411889573167104 + d *
    (33562382632995101008760164709663979046645647006453575450624 + d *
    (-63058254225694760494450532619717344270914521822915596910592))))))))))) + d ^ 12 *
    (69094400335396773021016156204110997026182204573317086838784 + d *
    (-62327181361111229915119890594550867266992494587864974098432 + d *
    (50210149301486366383828048480635965077552990333701392171008 + d *
    (-37299840803629719162449830695742587082977016507771103477760 + d *
    (25943280132729349205991884115581145223573545722188184682496 + d *
    (-17017689410885010926421662351407385641089683741081356206080 + d *
    (10551605465518016186415781440348868209555375366822810877952 + d *
    (-6170669423755719842449573612771125252317915925765714083840 + d *
    (3376870706116635037412956940952091932542101247005910630400 + d *
    (-1698403225641295556065657217162535906636740868848879665152 + d *
    (752782414927845898234483929024695213056442273037135118336 + d *
    (-259517182666314992963089009480969657864696505807018917888))))))))))) + d ^ 12 *
    (28191975147940354571103972002800008963736032698146750464 + d *
    (62051759021986830446455681046991636618137766658292318208 + d *
    (-83091472247331916409756282920696598712545352515293020160 + d *
    (74785156896883065824744721629683195417314630897965465600 + d *
    (-57432731731688067557528570697522581212178167634234703872 + d *
    (40187828962523456227051559130900294386957997991942946816 + d *
    (-26338451388452657047194412043066489696072283243856789504 + d *
    (16396904680097319901157331987593381076319863342658486272 + d *
    (-9774596350579431429374099864277272570906907254834331648 + d *
    (5606861749685143638195884660516227768034260875387600896 + d *
    (-3104150105278581471691496681543969200912560008036352000 + d *
    (1661762474357415387113857179823664364939044675701702656))))))))))) + d ^ 12 *
    (-861056914142902590570211836143682592885069489276977152 + d *
    (431986470826381819340999872034414294662857780095877120 + d *
    (-209774991813161620754978756098441407839976049401659392 + d *
    (98507495740279660826339965034875337064697510388301824 + d *
    (-44653893813077377202609847189592773699813840821944320 + d *
    (19484651146766939501529505767162038075599176389885952 + d *
    (-8147331078065428354091344484194551335099259884142592 + d *
    (3240855265944169857138442634834500693254773469872128 + d *
    (-1211103557888745184678257550571642413670126138425344 + d *
    (415159414549214769237041569836350434807845906022400 + d *
    (-123657649775057289018515458113193149548175301279744 + d *
    (26852498507270406536854802995226618793649354833920))))))))))) + d ^ 12 *
    (263708494278396236397747738585595793363312836608 + d *
    (-5091815791526443068153572057075127921613967982592 + d *
    (4158064715580883088601154691694684942864245587968 + d *
    (-2512347526146674866664715862826026367355778498560 + d *
    (1323659936103852117572202148940772364701570170880 + d *
    (-640487589395478570996712297398077516898783985664 + d *
    (291247348387219206994955479312505328922137460736 + d *
    (-125963822056096648356188134954861753835370315776 + d *
    (52173032565886030176809121463826728570759675904 + d *
    (-20779986022720922237483679319566156017399234560 + d *
    (7978214885674660251345027822664213018908557312 + d *
    (-2956730365715013936448148628941077432537186304))))))))))) + d ^ 12 *
    (1058265937091480878672736269856230866272124928 + d *
    (-365765365873685439360605689866392554951409664 + d *
    (121994696283071487137267308957177967327313920 + d *
    (-39219347261391932581258701087885176649023488 + d *
    (12132763423316021058474619505718340498751488 + d *
    (-3603779180733761467933363496233275752448000 + d *
    (1024784295167678716056531942184402579619840 + d *
    (-277925639676159889369367484447269883740160 + d *
    (71530956287375007383461997396085243379712 + d * (-17359465346806995061025424209670593576960
    + d * (3939161284145869200499359199748969463808 + d *
    (-826427898672694414923960565687870554112))))))))))) + d ^ 12 *
    (157804369965634092991629640389073567744 + d * (-26793837339620727029745783649406287872 + d
    * (3893948217426470890546277451544657920 + d * (-449363864095693601047445582978220032 + d *
    (33072811106608399674903319413784576 + d * (462481579130101450469728431112192 + d *
    (-563602349153755199461916981592064 + d * (83265820911729214058934302146560 + d *
    (-5282545995603971111622105890816 + d * (162623359368354195953060675584 + d *
    (-137721266272247864418603892736 + d * (52794746810542157111309107200))))))))))) + d ^ 12 *
    (-9340036665742530350240235520 + d * (736869578446662445491290112 + d *
    (34582335176753827748511744 + d * (-14873600367723739164180480 + d *
    (1369293826529943235592192 + d * (-6533867822427571224576 + d * (-6883786475818996465664 + d
    * (157700287725158006784 + d * (11690177340771401728 + d * (4913229549694615552 + d *
    (-304552234830528512 + d * (-55425455989719040))))))))))) + d ^ 12 * (1609163272617984 + d *
    (345162089496576 + d * (16128733872128 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt23 (d : ℚ) : ℚ :=
  524440360823894636922770104842911129889423931337 + d *
    (-24184786524267711309223613087978412669891937303453 + d *
    (6219426508271262928395735446711344226465903397141 + d *
    (47422468797109056394766798759182653362270469271277 + d *
    (-77214631451381979419038998034286142115461916567776 + d *
    (88841547675621741519742447209756274185927286728999 + d *
    (-7580876433472084313695432028380023963025972102465 + d *
    (-160594590261341366188068016691969161528030894153648 + d *
    (287207604098770035391114405239861772752854525179212 + d *
    (-279281026910083843999212187602553675757847220333238 + d *
    (108929738670698544085263502663408324863097772796806 + d *
    (185681756351614858186170944927130038593972238925293))))))))))) + d ^ 12 *
    (-462042050772855360284611608576631230256149353567880 + d *
    (561086562283470027969561346756632593088627077652026 + d *
    (-422819668127350458489750903999219948457057582769505 + d *
    (90706379977474477754997858883023316834180918895342 + d *
    (314592653857533144918634913559148959839163779838242 + d *
    (-635711556263458100077961752849850805235095356597612 + d *
    (755564626397123565188379591207148710478624925561033 + d *
    (-646297648058486529396990352582398535771603117866159 + d *
    (361085171659424722806943795299201614932726012555467 + d *
    (-3289787068827040240869395485553466623331960844281 + d *
    (-313788427821021808744181173922884581453189684690145 + d *
    (509028981086201571217512060430275450880679122964198))))))))))) + d ^ 12 *
    (-554468071394090280357679533340285004395434571786432 + d *
    (470261867709361618242395662702110633742302719753940 + d *
    (-306648109208023577249962179034871248051247582634953 + d *
    (122028463823129315820418514764172573007488504022313 + d *
    (36207479801071134576697528454081555642228746639407 + d *
    (-141541964046381501970753374190195104078118468186625 + d *
    (188347378891605136263843927343059796999944590079946 + d *
    (-186225759623218164022063317257520100820421846099519 + d *
    (152388911828374565609599589536957758951662741228889 + d *
    (-104702796453200293339477870804530304933492649315421 + d *
    (57221207293179170451659309787811439730435351458488 + d *
    (-18524721413772936195985895501502130116563354344724))))))))))) + d ^ 12 *
    (-7949099450325422949493829221059129885924453536194 + d *
    (22532482697976361513055134726376104089411698536956 + d *
    (-27666151364850281348341270242478125939241505477995 + d *
    (26488423792994693666004639458266807436365989758780 + d *
    (-21910426192866180890693568724728965517810953983751 + d *
    (16158521769697174295379808049709587258808116088397 + d *
    (-10663315294749742177897114873026916947550399911511 + d *
    (6159819388533142485591877778616558722989330784127 + d *
    (-2877999759359393191997392199181207510486997935780 + d *
    (739501708740448712360810257660530272706834891387 + d *
    (481929272450427300616704442144990052822322798907 + d *
    (-1049873341147725513918086358450249701315279101691))))))))))) + d ^ 12 *
    (1201879116333786245279379724111444013582801631762 + d *
    (-1122360434212151850943960990153083680184477041999 + d *
    (938648020864404158616228474122192502395329660339 + d *
    (-729128356534301591246316789569713167795196123970 + d *
    (535751974414221075510430807597697047715844840919 + d *
    (-376311417174797986445269530795720741033331789519 + d *
    (254344607314343445819434687918776385952557923528 + d *
    (-166146206455909968538685343397450441243504814402 + d *
    (105208561018378880241694464756167113558791566580 + d *
    (-64715043107269131080058616114348864635104079251 + d *
    (38723341533290241706233350167744657911053543476 + d *
    (-22561312401846316538820115957881475496199523721))))))))))) + d ^ 12 *
    (12806392641017280721364894977754936158866884283 + d *
    (-7083932639047633739927980886641695405547410564 + d *
    (3818627020256125129376797385008102428873987479 + d *
    (-2005479838477966726343369785209084823541611729 + d *
    (1025631521131806798102596355590638068450252683 + d *
    (-510375050302131425716963059294063464813749058 + d *
    (246848330302935123225988992814872168678074541 + d *
    (-115862166487960812790744112248588556083538549 + d *
    (52660907965628393307829987488451277744156922 + d *
    (-23107171629673822402217987917462776346975085 + d *
    (9744991465288403248252336954664871898535797 + d *
    (-3922965234103557863567434409940611987814297))))))))))) + d ^ 12 *
    (1490486918612818690609504266124951367283228 + d *
    (-523520672205179366461193348713495554239974 + d *
    (162605653839686052722476229292437849599019 + d *
    (-39268145961105127914805413655333574846401 + d * (2840504660106586662766986568823719992624
    + d * (4826679605051003111850927801557125212283 + d *
    (-4523087365586123398095276327308118328522 + d * (2870167310157518321542620175166905703614 +
    d * (-1555966645590738262382461526808379740361 + d *
    (768542283156003486268123422901238005897 + d * (-355337276394254970285034597579777437451 + d
    * (155911141031150741883353532228982171150))))))))))) + d ^ 12 *
    (-65421355099246587318593795041311184874 + d * (26370782964183723791791329321642288911 + d *
    (-10238165835738988662992372151888871678 + d * (3833790871357227787963825202053807101 + d *
    (-1385449775630336037432402230118906546 + d * (483130715291911889938975254054083145 + d *
    (-162449037964646425827443927774979120 + d * (52590890608517352465106812740651357 + d *
    (-16357179018104627354637762433918024 + d * (4874283865930556603074269964535136 + d *
    (-1386926385999758358619636269819079 + d * (375199502914110872731054227157078))))))))))) + d
    ^ 12 * (-95917296606382839184610474697405 + d * (22963141067690339245474854546028 + d *
    (-5080508991185194227250911678878 + d * (1019563463620880952706220502137 + d *
    (-180859060837409019185468272796 + d * (27324511026864578045091384046 + d *
    (-3308847888002579815628588394 + d * (282367549829217322480680290 + d *
    (-10190406730066392669582699 + d * (-943595503838131781927362 + d * (83060450386924084589330
    + d * (13906756517909946384653))))))))))) + d ^ 12 * (331070410966400900162 + d *
    (-1486358881185759129648 + d * (398895011533997100036 + d * (-52674316736739149855 + d *
    (3022496945426455983 + d * (130658416739525961 + d * (-31049905629010227 + d *
    (1136317622729020 + d * (14038730433543 + d * (11345863144155 + d * (-579586791033 + d *
    (-173371142021))))))))))) + d ^ 12 * (5072991061 + d * (1234676212 + d * (58452094 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_23 (d : ℚ) :
    orderSevenSelectionPolynomial d 23 = selectionExpandedAt23 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 23 =
      selectionNumeratorAt23 d := by
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
      selectionNumeratorAt23
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 23 =
      selectionDenominatorAt23 d := by
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
      selectionDenominatorAt23
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt23 selectionDenominatorAt23 selectionExpandedAt23
  ring

private theorem selection_cofactor_eval_at_23 (d : ℚ) :
    (selectionCofactor d).eval 23 = selectionCofactorAt23 d := by
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
    selectionCofactorAt23
  simp
  ring

private theorem selection_factor_at_23 (d : ℚ) :
    selectionExpandedAt23 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 23 *
        selectionCofactorAt23 d := by
  unfold selectionExpandedAt23 orderSevenDualKernelPolynomial selectionCofactorAt23
  ring

theorem selectionEvalAt23 (d : ℚ) :
    Internal.SelectionEvalCertificate d 23 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_23, selection_cofactor_eval_at_23,
    selection_factor_at_23]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 23 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt23 d
#print axioms solution
