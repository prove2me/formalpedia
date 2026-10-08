-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_22
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:43:33.359524+00:00
-- url     : https://prove2.me/submissions/7b1edeba-0add-4296-b746-0e42eeb67e25

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval4.At22. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 22

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt22 (d : ℚ) : ℚ :=
  -23238522352049618944 + d * (-3525863416229670912 + d * (6984808048079718912 + d *
    (-15364468843272006720 + d * (23610353469873510528 + d * (-14915606115577840128 + d *
    (-963310391063378496 + d * (11337641038293416064 + d * (-16252618272764999040 + d *
    (16776304375331079232 + d * (-12040784018916511680 + d * (5816968057940757696))))))))))) + d
    ^ 12 * (-933334178054394048 + d * (-2405045613507140928 + d * (4289756652594580608 + d *
    (-4686663980367783744 + d * (4110475664976194688 + d * (-3183189528763135296 + d *
    (2233074300969033088 + d * (-1425229298147644800 + d * (841402348912651968 + d *
    (-467028965919832512 + d * (241393297066880256 + d * (-114034215977210880))))))))))) + d ^
    12 * (49630916344165824 + d * (-20504689686816192 + d * (8006016139436544 + d *
    (-2783327489337536 + d * (825985327213440 + d * (-229404547977792 + d * (74004597975360 + d
    * (-26045169917184 + d * (7361438984832 + d * (-1422358940928 + d * (253352498304 + d *
    (-89608157952))))))))))) + d ^ 12 * (31637426304 + d * (-5802014400 + d * (364944960 + d *
    (-55176640 + d * (49550400 + d * (-10585536 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt22 (d : ℚ) : ℚ :=
  -27540804885495644160 + d * (-4471678060529219584 + d * (10665143691290159104 + d *
    (-24590112815950150656 + d * (39392946626958245888 + d * (-32699344468324870144 + d *
    (13743091379169632256 + d * (252191635839667712 + d * (-9471910280136254976 + d *
    (16265634655046134912 + d * (-16578371959686557312 + d * (12517094387636564160))))))))))) +
    d ^ 12 * (-7821817632351279872 + d * (3547241145218880640 + d * (-204423402399420672 + d *
    (-1479020545019110720 + d * (1793626990861114304 + d * (-1518875448604257472 + d *
    (1100091764164937152 + d * (-710697850175595200 + d * (430254525863380736 + d *
    (-256799583828343872 + d * (149667155906562176 + d * (-82617276062610560))))))))))) + d ^ 12
    * (43702291965444544 + d * (-22786507824604224 + d * (11602547348444288 + d *
    (-5615365060352640 + d * (2575442110885696 + d * (-1128936452638272 + d * (467662969538112 +
    d * (-179327413776832 + d * (63675452934720 + d * (-21229608934784 + d * (6525859289984 + d
    * (-1718349126656))))))))))) + d ^ 12 * (347039025664 + d * (-45246231040 + d * (1984183296
    + d * (391383040 + d * (-51969024 + d * (-1338368 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt22 (d : ℚ) : ℚ :=
  2588037032583676660054658613053983060085996449904988258304 + d *
    (-119526655136828902945363740195332698770694987069401140822016 + d *
    (42302458879054007648101038279548662706224576935083613618176 + d *
    (217889692850754089655971125243923202018409915422610663931904 + d *
    (-421750289219296885651516296258432563137962823577958875136000 + d *
    (582461000665692166428618763367181863488085490924362590584832 + d *
    (-219142763489197107666406543361959988899621264386058602151936 + d *
    (-766795177084548938700247173396748373554660023386897383424000 + d *
    (1770879412658383170781810545151852189133503568840572002107392 + d *
    (-2164420121205563639140915227664356532343884760154487199105024 + d *
    (1452934271307853117451437156911377774048497932805759456509952 + d *
    (487910216902115169799593990599760851112277709963129297305600))))))))))) + d ^ 12 *
    (-2914526344075263808670249363794243042878134880946256921755648 + d *
    (4586064846680632904110977126728213245991837639689155945168896 + d *
    (-4540418073480359572065673866020791350134555876034710371041280 + d *
    (2455556608835927296421467132973322313766231968107050492493824 + d *
    (1134170977241254950632643114283090331061257239403893623619584 + d *
    (-4929829069138657725874915222471446663796975658388561530454016 + d *
    (7484760632592925236446763861373917175229942585948270943010816 + d *
    (-7845302824394010863826334348631052010709520634640857588039680 + d *
    (5858665876892357620508053990146294776382560919136866494054400 + d *
    (-2190471054635945625808589908383115456607930447317520885219328 + d *
    (-1960229766207553611193235457673586861985793286309588971814912 + d *
    (5357198224019927505457677728502765241409001637703546408796160))))))))))) + d ^ 12 *
    (-7154316176175193280918637441890578939711412284436858101563392 + d *
    (7094780399323336066437567611960761376832810920096378473152512 + d *
    (-5487976889794729699736301029600925879950179397845158390923264 + d *
    (3009726287061014268371600802731316788446299579304941677707264 + d *
    (-421481811528964525761096316274417269660928718721355591188480 + d *
    (-1666733907022680340406680200386222438662125483628605059891200 + d *
    (2921742322791789964861744372287162716942545789293934471544832 + d *
    (-3299435305704391080715523887327585694072822643720156476866560 + d *
    (2972744606632869024256076569781303749683496939428612653187072 + d *
    (-2220827248690457842827360321808736221222626659963288375787520 + d *
    (1326173905012997077838636184847609256464782210408847355936768 + d *
    (-506848529034251448782056919470801832725414656927463508541440))))))))))) + d ^ 12 *
    (-110996646620265380819932445836581837175135472869020356313088 + d *
    (487974425940496387984072356973360448504409286463649992671232 + d *
    (-647208636585533449653915040497457736869101141294301758619648 + d *
    (644922634944274287389591868371016678870373549592120088068096 + d *
    (-545470555528831745545234263604478031630214629691774766415872 + d *
    (404918944429841734190585824198535692863438413669160661286912 + d *
    (-263363251075921589361567331758276771477018685900093173792768 + d *
    (143976941150779959773305381995781564270949966277352300216320 + d *
    (-56003552473909388599961632267917738385250539454616272371712 + d *
    (-774543071219071932268782084466142367518253063625084764160 + d *
    (31723789488395852614491177723282778383540355031166523539456 + d *
    (-44028847139760021522563166374928745786045739938545739497472))))))))))) + d ^ 12 *
    (44570108875629472202681446412104925687999249594815421612032 + d *
    (-38864957098323566739902334325878747754523032723237880201216 + d *
    (30769874222710920102934021706968143396351594707930825359360 + d *
    (-22631570553863171641928216880065549576931879200160198950912 + d *
    (15637686208225362869155396873157555061504448964472470765568 + d *
    (-10200370471320051606721590447382455298612848590992447635456 + d *
    (6283033064133439412018053192262387045528881722790382403584 + d *
    (-3637937862743979548418942309986035030867580814942207737856 + d *
    (1956736461743371254064048108147914538437529063848400912384 + d *
    (-951969754716783382091300214209313667542330883188878737408 + d *
    (391454427911480025668209374179226071371225350243835707392 + d *
    (-104789142477268090748741319526866545511893257692233596928))))))))))) + d ^ 12 *
    (-23969503622327605750650354824613579191628483650660597760 + d *
    (68565802398071569136778767911404785131051626928478355456 + d *
    (-72871629428150029440384686647612927182264644947893288960 + d *
    (61125734523446602491193850165222860110832365702849757184 + d *
    (-45523382410967474195384963536239861736502313431174742016 + d *
    (31384872618848471545746209095743770398290891623798407168 + d *
    (-20426024667408545424210352010039212396299861380525195264 + d *
    (12683649301277405361969930252093515273882460430182907904 + d *
    (-7561954477317615531963236701882368349609764221587030016 + d *
    (4345533944818437295110025554460789864608838550878420992 + d *
    (-2412807072097686348700544716582172138992607243413487616 + d *
    (1296262430403160670287584015821969833852416180772929536))))))))))) + d ^ 12 *
    (-674298869750309588812369960357739272141011953408540672 + d *
    (339646507031759766283655793684951080650591682904981504 + d *
    (-165569249184033271875952578292358395778892719309979648 + d *
    (78015074069988429992983146381092235230773225563357184 + d *
    (-35458211324071232623169236840762787295798427391098880 + d *
    (15493531828662301104340651964367509704667417355223040 + d *
    (-6474210557851412886464776625900801451527014827163648 + d *
    (2564814057019672008817731004673578398107227868889088 + d *
    (-948626337056936376358357880386652337123166779867136 + d *
    (317687320398995584596438520716548283956034016641024 + d *
    (-89283596030644147107046553082997086879716650778624 + d *
    (15476268840251052225033380574868359101792917651456))))))))))) + d ^ 12 *
    (3721387770676784086775854949211296491780684644352 + d *
    (-6013103262577905356923347010728723157089516257280 + d *
    (4345877099537642234310924520851170290278445350912 + d *
    (-2522000643427170895661928780445135443283233472512 + d *
    (1305755736452943954812796451889278646655393726464 + d *
    (-626842654364414334843868335623319406432686440448 + d *
    (284161030375363141361493029821576128786104057856 + d *
    (-122852121774022760503862213947465867119396651008 + d *
    (50947856239622746266159658549840384775896432640 + d *
    (-20337922103891698121954879948056825776417538048 + d *
    (7831013475296262843232167731556781414352420864 + d *
    (-2911592844850049170940310958462160015840509952))))))))))) + d ^ 12 *
    (1045672775535515369969929373939404900202971136 + d *
    (-362662320426238696333119946453428016680534016 + d *
    (121370265492990045920170330270793866174529536 + d *
    (-39145299917276389030974659003135022671069184 + d *
    (12146461187835772251983100768550613740158976 + d *
    (-3617663612588079448022336291633796366729216 + d *
    (1031141239261067165850713637353533274062848 + d *
    (-280178028774457747243948424515838796890112 + d *
    (72209477635434173262040731470136304992256 + d * (-17537941990933286698582685919984890675200
    + d * (3980242255602060518197500079998606245888 + d *
    (-834592875564928367364744400259596156928))))))))))) + d ^ 12 *
    (159164227227694274527495793177491668992 + d * (-26972750423192264136533141636012834816 + d
    * (3910168260640106263275102632202993664 + d * (-449947329839325559615333808718217216 + d *
    (33034510709046935712880362662133760 + d * (447832037448805738203417724059648 + d *
    (-555101473299451795811335135297536 + d * (81556625253883598436773083480064 + d *
    (-5137237105457775101074050121728 + d * (173119219365744876244656193536 + d *
    (-142307058996540255077297815552 + d * (53324674907145303874602008576))))))))))) + d ^ 12 *
    (-9350821372353366970022494208 + d * (733079915207156419201597440 + d *
    (34887876491341671535476736 + d * (-14862932042208083975340032 + d *
    (1368767532275276884738048 + d * (-6816581165454497677312 + d * (-6881217987464076197888 + d
    * (161109722249036562432 + d * (11709587702252568576 + d * (4893976910101741568 + d *
    (-305770011373862912 + d * (-55471541496315904))))))))))) + d ^ 12 * (1607844668375040 + d *
    (345147765948416 + d * (16128728629248 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt22 (d : ℚ) : ℚ :=
  121184992592499912653217117044446022436386766848 + d *
    (-5580097770362843909588057782999118913341052944384 + d *
    (1176924552674115544944959642462671039067990261760 + d *
    (11901260234242561089959286752777913076094985273344 + d *
    (-19520335128197357110086168814003240805667600228352 + d *
    (21710248692015332417901326901442775713685200108544 + d *
    (797476359407374052606078658509313942333367591936 + d *
    (-46242275987155414437539330854941724611844105295360 + d *
    (80288830346263439909461673707607624989985150218040 + d *
    (-75848104649282735031207287655080947993609923729117 + d *
    (23471700982538923282071856873462880324819671315062 + d *
    (65348461461457725578575183014167023387074400016063))))))))))) + d ^ 12 *
    (-147523766062020203352003920909958161357427682611627 + d *
    (173922194268484914343054486244713318513881229557856 + d *
    (-124186971981539577255991632897986213452251737213417 + d *
    (11322112739800692451290572909042695085205123337238 + d *
    (124694798576076862638685775767945044032983631640750 + d *
    (-230603505284376385208452191139497171942507710542870 + d *
    (265683906925402193846622068056934252388235323231898 + d *
    (-219253075507779100818327638669632992721939050709464 + d *
    (109801023287519075531228072142585628860129799039050 + d *
    (24968302292524870699237899576026156213769615357673 + d *
    (-142852448995688283526375167900002597700755352430366 + d *
    (212943390248292840320627753377452711318778750958776))))))))))) + d ^ 12 *
    (-224136534894057841901878437428087772794139845927063 + d *
    (184139266921177721473640586354435872122610055291216 + d *
    (-112978663556656375323794887766976885866172223643267 + d *
    (34389933719442329338857861193500323746027102404440 + d *
    (32017387009164956096649116119998098151466886267897 + d *
    (-75066037687626881064204675669994416139761642593857 + d *
    (92365596039416940770947561234140992928419828589277 + d *
    (-88149790006548865961753429552866354342382458581172 + d *
    (70084577558197969106979844712044308366769596455695 + d *
    (-46231565392032712306944666797920887223446263085781 + d *
    (23013155222499772582016732657115109329292507915946 + d *
    (-4382976205168181683913474056450557027798834154771))))))))))) + d ^ 12 *
    (-8090352441154553045201705396513390192910112632270 + d *
    (14624198897782150471335151317594363672238951740317 + d *
    (-16456670720565510324891516199234344809448801206802 + d *
    (15174652805479240036693689252033295182858227284715 + d *
    (-12258038818092873008987835992549306166705882638926 + d *
    (8844909222915937518246820009770975010532697336371 + d *
    (-5668354655867409299087293686964179519211508775385 + d *
    (3101867399249758987413694862851485397258263831881 + d *
    (-1254069202179103948432993656989282611130182892501 + d *
    (69917952902984106634404411016329910847860454943 + d *
    (584689530174937830748733991425812230659152824097 + d *
    (-863388046670560922394812113087983503201763218183))))))))))) + d ^ 12 *
    (904515879372507091524857475509378424744451067351 + d *
    (-815798170351922590669554906866943309550053888323 + d *
    (671862922150847640557369596926471796472429860456 + d *
    (-518689958347978689673053603613065442169446088463 + d *
    (380715289363480580643267652496943462250756920013 + d *
    (-267950734523536129396130410179392855792982446050 + d *
    (181828981811119784885467420258859976574512036993 + d *
    (-119409881110992400862699230295256655081251247690 + d *
    (76085692103971594169783731474541057614705189665 + d *
    (-47122386847620751247666031404586348747700797404 + d *
    (28401656321889682997695287397115309769968097969 + d *
    (-16672318166700979011352691014501397389931558735))))))))))) + d ^ 12 *
    (9536288023761655707100456498228350183041566648 + d *
    (-5315759062367624026026802184746174945576433435 + d *
    (2887459760643021456663588508800854933960726624 + d *
    (-1527876131953070061076230284780163748866408513 + d *
    (787096832753501426219959779520953605025331624 + d *
    (-394417687596927450097346651820155280921649009 + d *
    (192016056793768614795039596554071102774780063 + d *
    (-90662775201049494139546989064487816136528835 + d *
    (41418498721066555386204444002904843707019745 + d *
    (-18245488280337927153561280410118306552062510 + d *
    (7711217972070041973469651351189679583166777 + d *
    (-3102181291220010347069495629055657724977972))))))))))) + d ^ 12 *
    (1172132157962098382416777766943175657421356 + d *
    (-405506916845428541091530692818548298588139 + d *
    (121151807503195016884852791345445658061605 + d *
    (-25667170861277012424305213402508226117624 + d * (-1215707278690303415911902062011517714570
    + d * (5858906394011006557521445019850264301217 + d *
    (-4702821659586319808848005502343185464028 + d * (2856817795317409677465053164876959481532 +
    d * (-1522076912098599171826457342844302207586 + d *
    (746450434621901051475384322384701010831 + d * (-344368065942251688167123801307100693853 + d
    * (151176700681466336093764548154735166733))))))))))) + d ^ 12 *
    (-63568180252513584671208757181384626326 + d * (25702086248903659227393937147625750638 + d *
    (-10014712743529780590505660326835418400 + d * (3764885751489433189339746211653833126 + d *
    (-1366082797510269527119568237597979842 + d * (478304659822231616402088944913289831 + d *
    (-161453733521285123139316327006063954 + d * (52460152975111227590623093619742912 + d *
    (-16371396815054101985761990145813809 + d * (4893198432307337061619468513843566 + d *
    (-1395876439523491398981516406171193 + d * (378360674701968756483886476406367))))))))))) + d
    ^ 12 * (-96837100996997321335265970192128 + d * (23187593621317359579443638961793 + d *
    (-5125930420127773634776769232528 + d * (1026929694714170733613963788578 + d *
    (-181748900262767304059472023380 + d * (27391144983024743411273925103 + d *
    (-3310304134968370217565324850 + d * (282638182317216055507124224 + d *
    (-10448740679539307533714355 + d * (-871844837256841474787331 + d * (72836371466011989547365
    + d * (14486087453482752655791))))))))))) + d ^ 12 * (391423948145875653835 + d *
    (-1500505562939345451582 + d * (399713464854005275934 + d * (-52642524396807386673 + d *
    (3020360831622821344 + d * (130109089897508066 + d * (-31056100560215986 + d *
    (1145263717818668 + d * (14135459755160 + d * (11285609431871 + d * (-583607253823 + d *
    (-173522330023))))))))))) + d ^ 12 * (5068544083 + d * (1234625412 + d * (58452067 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_22 (d : ℚ) :
    orderSevenSelectionPolynomial d 22 = selectionExpandedAt22 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 22 =
      selectionNumeratorAt22 d := by
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
      selectionNumeratorAt22
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 22 =
      selectionDenominatorAt22 d := by
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
      selectionDenominatorAt22
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt22 selectionDenominatorAt22 selectionExpandedAt22
  ring

private theorem selection_cofactor_eval_at_22 (d : ℚ) :
    (selectionCofactor d).eval 22 = selectionCofactorAt22 d := by
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
    selectionCofactorAt22
  simp
  ring

private theorem selection_factor_at_22 (d : ℚ) :
    selectionExpandedAt22 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 22 *
        selectionCofactorAt22 d := by
  unfold selectionExpandedAt22 orderSevenDualKernelPolynomial selectionCofactorAt22
  ring

theorem selectionEvalAt22 (d : ℚ) :
    Internal.SelectionEvalCertificate d 22 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_22, selection_cofactor_eval_at_22,
    selection_factor_at_22]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 22 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt22 d
#print axioms solution
