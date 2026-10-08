-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_30
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:37:33.860159+00:00
-- url     : https://prove2.me/submissions/3bcc4ea9-e39d-476b-aba7-cc0b1f5add7a

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval6.At30. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 30

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt30 (d : ℚ) : ℚ :=
  -949282431552000000000 + d * (-94303501725888000000 + d * (126904590152698176000 + d *
    (-281474594179786552384 + d * (497985974627318481024 + d * (-332102543231000080896 + d *
    (54080351565843610560 + d * (79060592659581101184 + d * (-127515586087811784576 + d *
    (145312865909877147712 + d * (-107046889338644488128 + d * (57617856790791530688)))))))))))
    + d ^ 12 * (-25275369390128782016 + d * (4704955199382434496 + d * (8358156272593901184 + d
    * (-12683075522416155456 + d * (11446595135365685376 + d * (-8691435899240882496 + d *
    (5910481818449539456 + d * (-3583186887706214784 + d * (1987280014754221248 + d *
    (-1047991549045222848 + d * (518048235068893440 + d * (-230761594784882688))))))))))) + d ^
    12 * (93570400480144320 + d * (-36767970828573120 + d * (14110606927451136 + d *
    (-4802396143468736 + d * (1336580895682944 + d * (-336128772603456 + d * (104789066548032 +
    d * (-37672996106496 + d * (10426407278208 + d * (-1814134262016 + d * (276495600768 + d *
    (-104772293376))))))))))) + d ^ 12 * (38447935104 + d * (-6660816576 + d * (313206336 + d *
    (-37979584 + d * (50693184 + d * (-10567104 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt30 (d : ℚ) : ℚ :=
  -1125050046912000000000 + d * (-118124152462483200000 + d * (200385686019707136000 + d *
    (-459099042143854033920 + d * (793825756008652283904 + d * (-635702010675552032768 + d *
    (280346834138667184128 + d * (-86704918214385058304 + d * (-12741928560070669824 + d *
    (103996434831474758272 + d * (-120473770185115248256 + d * (90380598239563804352)))))))))))
    + d ^ 12 * (-58847789314729985280 + d * (32433282877342304384 + d * (-10679199626273065216 +
    d * (-694299494100336448 + d * (3513437040340011968 + d * (-3264584836524264128 + d *
    (2418450036486551488 + d * (-1515695721967844544 + d * (851588367994665728 + d *
    (-480175791309675072 + d * (268860629388957824 + d * (-137977067719931008))))))))))) + d ^
    12 * (65903797991258560 + d * (-31825227087185472 + d * (15497602085842048 + d *
    (-7099164658444928 + d * (3027616829327680 + d * (-1252169077704256 + d * (501662728540224 +
    d * (-185512163780544 + d * (62500388383296 + d * (-19980859215232 + d * (6140008016768 + d
    * (-1664714460160))))))))))) + d ^ 12 * (346478180864 + d * (-45803311616 + d * (1971674112
    + d * (402507776 + d * (-50846720 + d * (-1330176 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt30 (d : ℚ) : ℚ :=
  176569170545537158952346265922568192000000000000000000000000000 + d *
    (-8216497394263505647121726578340479500288000000000000000000000000 + d *
    (4734399175798852036339616813249217640755363840000000000000000000 + d *
    (7743968653535929322554115174479274476108774637568000000000000000 + d *
    (-13785482242162755543856946675157184241336666483589120000000000000 + d *
    (22226860103877149276693144249836341746234425929223372800000000000 + d *
    (-16947775569058573216623174650143253198049926827784483635200000000 + d *
    (-5034334560129124457135458132870682142897157963488597481881600000 + d *
    (25826425994595047028041175239045659236409092445521166856355840000 + d *
    (-36533693936342919956247920604447557910937301263426791285404205056 + d *
    (33770182647484777876470485740692340258938354255490287913269985280 + d *
    (-15304825779996347202171881207195753114761381888010265662260248576))))))))))) + d ^ 12 *
    (-10005225578754138432350361774501675483064922895382765515755749376 + d *
    (29081964578093724952983247330118465124391989834556445286056329216 + d *
    (-35920715380840649217475604665882194787341554589711910933847080960 + d *
    (29813433511393487100365869179230988709645847908754170600826863616 + d *
    (-14035999134108174231719713526532485808387375586019905568903528448 + d *
    (-4220519398776848254695910573357013531390772920662084125048438784 + d *
    (18153779935217235968168795893076352602479400655071870223701770240 + d *
    (-24536486520088623943403092766744055386595739883179212612514349056 + d *
    (23286799126622431204436057611828181157565699775448179155840532480 + d *
    (-16557687078379679944998508664585122382860362693888157144055021568 + d *
    (7716674562851934428254153862053555826889512062994843670273327104 + d *
    (228132477126705310855646400407634718178329372782652388703469568))))))))))) + d ^ 12 *
    (-5568729323762460563410765729414661018277179292977571624470183936 + d *
    (7877257304873678031832515339267862574123306308249095116996476928 + d *
    (-7660767736601348083217735233331334883137693983583848843715543040 + d *
    (5916272716600095638974031611276494184649387455251959320888213504 + d *
    (-3651707985150547253874078909000659629061381822187560990379343872 + d *
    (1588526154468247683805487729600385789433442013584703110826950656 + d *
    (-97229806307538978478365506097982858495458959174091292846063616 + d *
    (-745251385391929085128032824988121361057906058165052891048968192 + d *
    (1050366103400788927053435607175219712405611073033493734696157184 + d *
    (-1003959976584204148728146539033793349976118861497134381492862976 + d *
    (783531033677475175338911722822230758672598794910818963736231936 + d *
    (-519704240473650797466221290933993393953822409207684116342374400))))))))))) + d ^ 12 *
    (288620233243044898831066486473499192994175626530702944010240000 + d *
    (-120936507161692768427503741002082885053166009280626380284624896 + d *
    (17790731534204628522855948547502163402665998421691892472217600 + d *
    (34000658664952319512945807828242195143734186341508168146223104 + d *
    (-51447577118982062565584263352618858731171067385305201459593216 + d *
    (49638240211549418773307041327147364413147308096028611706355712 + d *
    (-39466239813458744528236746781961244664067305476648698354073600 + d *
    (27551631222185270748754682897315214715561939047650902244589568 + d *
    (-17193917980240318064746956371694065260378850538481413697830912 + d *
    (9529474948740962589235055060594659444051941637667206445137920 + d *
    (-4507258863315039779798453007533277973372657479341588055064576 + d *
    (1573603237618145220614403506027817411998399702459321273024512))))))))))) + d ^ 12 *
    (-76785643076890819158934001087398066314278263180553437577216 + d *
    (-541288330950810694257962007584611125037442628867163438186496 + d *
    (684962746022442102379578038189304036843635027755400858435584 + d *
    (-612212044065599196010808740855906464215532929969801403301888 + d *
    (468749707728685058772898349466069445974405768994074296320000 + d *
    (-325752053003834180346759200606192627602925296155910096289792 + d *
    (210625442428454008786718942850949756947706120409927636484096 + d *
    (-128259190403728082024814432585100671446111879382205585424384 + d *
    (73974019890366136994169399335001525870905652887800208687104 + d *
    (-40461445476354682613209090643640962780355821531058574983168 + d *
    (20929307479131998889877186531467904821217267882656323600384 + d *
    (-10153570073475598265109978375478628891274956492927858376704))))))))))) + d ^ 12 *
    (4536561086717111363852229503531864393437234690514684477440 + d *
    (-1790408275838616317265649993116549923999883488056725471232 + d *
    (552165575441171413891679371128268539971319656327562657792 + d *
    (-56614327034503144190618193057538706242117112438329704448 + d *
    (-101199324487273668650065087160009271479546329733929369600 + d *
    (122142031269004073052096277711021223459191681836593709056 + d *
    (-98289117125659138227972444209565625830287907003866021888 + d *
    (67382059104781345375037916827158636830769023958055911424 + d *
    (-42064628639041845974459777461594973300899201042293719040 + d *
    (24586781184171630779165688255968230917809278189327613952 + d *
    (-13646925529497187915013120426834396866038193859580395520 + d *
    (7250992700298904847347441052455445175910454348038537216))))))))))) + d ^ 12 *
    (-3705833296491809242612000240284996467334988317207822336 + d *
    (1827178472881797245319564044622059613352492239333359616 + d *
    (-870625383137980527848588759708559660672763856274587648 + d *
    (401237487419544436764016082702047866663447625724592128 + d *
    (-178870405145656990676277962436906549434857417237069824 + d *
    (77086084489076506071490012473132162261554136758878208 + d *
    (-32069153549140693947605172084167214178272638149328896 + d *
    (12846421173450776528278875160025009521043415774265344 + d *
    (-4935104417768759203682614762174397435342168095457280 + d *
    (1806186508511654188820329387352142774484028729065472 + d *
    (-622695162390874079184541261735193456873114296909824 + d *
    (197988692780929457105402521981003616892417476657152))))))))))) + d ^ 12 *
    (-55424676322808731695985718167753525680647690780672 + d *
    (11896709952237463891441587823408079913323855085568 + d *
    (-595439654043022411231936585372372028878454259712 + d *
    (-1348136298772411706280781260266933360544289914880 + d *
    (1105895141530748092377497315574738300289198850048 + d *
    (-630204755677409984802386294672869292109889011712 + d *
    (308533374282682538323086375859858211066763804672 + d *
    (-137921825362026686764320899027563239661240844288 + d *
    (57769864183523163521451420522690839707463974912 + d *
    (-22973318135393464545391091470674071262798807040 + d *
    (8738053319777637169660421096510988796453453824 + d *
    (-3192760317107491397086995014409358018307686400))))))))))) + d ^ 12 *
    (1123489131696369114442863348131022149008752640 + d *
    (-381203460126724745577539041379584386969370624 + d *
    (124751499518560637878208272844724469344239616 + d *
    (-39357886961882869893165071800552954890027008 + d *
    (11958025484601945725765604602631908534517760 + d *
    (-3493268769241015935703652024454618740162560 + d *
    (978924738987350124102070825808104578875392 + d *
    (-262301157737301414895450134750381177307136 + d *
    (66903408877118753859321266785666275213312 + d * (-16147755472433587721078941728987904737280
    + d * (3659072048572390226062165195387090501632 + d *
    (-770137463598199873449443167716501356544))))))))))) + d ^ 12 *
    (148268831027707409034642330537174237184 + d * (-25509840559957699501761521253718687744 + d
    * (3773567198255683381612056902272286720 + d * (-444709997405770468408695352403427328 + d *
    (33414867438327878594219273291300864 + d * (534910568194838132583156500398080 + d *
    (-619015619711407329311657164013568 + d * (95085478990196427391989987147776 + d *
    (-6335994606559946937825432961024 + d * (94301761298878502432291160064 + d *
    (-105659829051749698311710310400 + d * (49052235932415110736591716352))))))))))) + d ^ 12 *
    (-9265232157104574137166987264 + d * (763795602013751737246023680 + d *
    (32460758344284279899947008 + d * (-14952924371411557969559552 + d *
    (1372782573960428736217088 + d * (-4530610038399225036800 + d * (-6899506401162339549184 + d
    * (133931384193038417920 + d * (11557133079504748544 + d * (5048033985955102720 + d *
    (-296027730647449600 + d * (-55102857443540992))))))))))) + d ^ 12 * (1618393502318592 + d *
    (345262354333696 + d * (16128770572288 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt30 (d : ℚ) : ℚ :=
  3337567982289047127274263000000000000000000000000000 + d *
    (-154973781506424180679509594019500000000000000000000000 + d *
    (73172947145002195306598379393985260000000000000000000 + d *
    (185112123887596340920250940421062356127000000000000000 + d *
    (-279694886767486456153812817446107767568430000000000000 + d *
    (370608828585609843204767390092570674964942950000000000 + d *
    (-195262716624424941271142470614122391240775762800000000 + d *
    (-243657276519538556386819402650676387021399464302400000 + d *
    (562197489228084490607936096897414070738059954361135000 + d *
    (-609967489818463027962412775833666900674372751716567509 + d *
    (409526156513543610369346970111839518432466373126544230 + d *
    (-13240941103551496704178172985700419504644768227876729))))))))))) + d ^ 12 *
    (-380155436797942796857769191536808182234091217266023203 + d *
    (566528041058939697483251603688777297652342416111371944 + d *
    (-517712335228868389269907100627263801049266185541949097 + d *
    (301846507861129060283900941422335504419221371377737606 + d *
    (-15754175887351924528861730459019363043479649175922338 + d *
    (-226759705286740372063465448232648034307739899751234782 + d *
    (351749576334662262239703871041461434868560711928001442 + d *
    (-353894366189466792148285045967865567819492072181281192 + d *
    (267343981817902940176550445848499164072964748839415538 + d *
    (-139970113047544940283841347348958930337825333978860439 + d *
    (19005059499605869089340292407132858852974875931599258 + d *
    (65295866262845304684010254976410165371593892686720664))))))))))) + d ^ 12 *
    (-105030111845206107075451297786338438058335220576987895 + d *
    (107292708095379182685584390206291859979928819915806296 + d *
    (-85898486958356075497438900280124312715245712169107155 + d *
    (55441591709932190829565332363125863309516656967128608 + d *
    (-26797553475191838810902360959054148174539422906954159 + d *
    (5518100726020776116610882865219659252097814077667679 + d *
    (7118988100457590654431571511812745608932004634276101 + d *
    (-12398863509314210179086081312641705399089862146231540 + d *
    (12705597831551159004308518830715977420453934364851471 + d *
    (-10410534589481542134307415288194026083196708148374925 + d *
    (7279393439319110068389199335816427824302299470832546 + d *
    (-4366399136234030860721168138708222584129402794859491))))))))))) + d ^ 12 *
    (2143590535644211042085054199421661358599455936065706 + d *
    (-691778159052188990298230022169336239353504590167123 + d *
    (-113387003614052571580191441869819502848438202563082 + d *
    (462570080956153187915020378163484163039384344964195 + d *
    (-535608624196273202414867015408248616601596170349294 + d *
    (469981849828521069226233691237758937439852694734259 + d *
    (-355187747417457738601842655517452993458538422885017 + d *
    (240552319681400473313869844369066796512903315839737 + d *
    (-147629415706442258229871778451506005173124585524621 + d *
    (81521364007535729391570307153466230929537889592319 + d *
    (-39167578618323901066427472804052762004564039293615 + d *
    (14641986591270144986843943829549014646219997854481))))))))))) + d ^ 12 *
    (-2024807401749558916614269556350853645039388501961 + d *
    (-3409399318863989474606231324398870891005643757195 + d *
    (4956165655261774853904766237723572357700794647600 + d *
    (-4677746854977776621372211740204331508075937358591 + d *
    (3735852914673089897076910088358256135408191912197 + d *
    (-2709640749929276735522659440575861017832270370538 + d *
    (1838792033198288275962320639211063322267439847881 + d *
    (-1185695886157305450537564161403338472818984569010 + d *
    (733104501159534823369952356589512423778665962273 + d *
    (-437109736333479706955849075574721187672526445620 + d *
    (252286381927751312052759936322008734927574193993 + d *
    (-141316542148246293981164119498300405689300304095))))))))))) + d ^ 12 *
    (76955344020794030998414123475053550197088671736 + d *
    (-40787215385811702398820581360518059581844723723 + d *
    (21055118132117686902628874813837073100983294480 + d *
    (-10590141683866143072180949741781734357440776889 + d *
    (5190238134593081461972797322522791875396100336 + d *
    (-2478142232524783509206108340064760743073074145 + d *
    (1152172551585624764170983532035219698834434951 + d *
    (-521236081095652463168160591405869202004060259 + d *
    (229190086103664365324784730416959749776806945 + d *
    (-97797241891294881056400740259104164751666894 + d *
    (40410233477285309384510653914997000759153577 + d *
    (-16119795276168279939389707617672071232851300))))))))))) + d ^ 12 *
    (6179537264807245410437883441447535482325604 + d *
    (-2260538024467986369931847103449636567747027 + d *
    (779921711205551089075932363147335662019333 + d *
    (-248406414692407224135228908410840759580192 + d *
    (69711238691022902216350082248425092254470 + d * (-15003904667547410927012352129113715974111
    + d * (743962495202612743091275964960032283220 + d *
    (1723303881324988134988435294080461464324 + d * (-1418414116454858171981934199983737629994 +
    d * (811881225377493043110946408013219490191 + d * (-399363391773045491853731692828255886757
    + d * (179413462438259219660234804964047862941))))))))))) + d ^ 12 *
    (-75539460000291350938922371760378605022 + d * (30200254974897775531915563353441300686 + d *
    (-11548096309944997708733734873184149720 + d * (4241084854627473379838726712137836926 + d *
    (-1499493276045764126105228532033891602 + d * (511047414832147047687693336168619279 + d *
    (-167950908936171956859289394580721786 + d * (53191667765386301252080271933830416 + d *
    (-16208115117413336188848305614680673 + d * (4739915746139947069236311918088598 + d *
    (-1326414058390539786992894822683385 + d * (354012672770569429553419859339567))))))))))) + d
    ^ 12 * (-89712370883521326475714295634568 + d * (21427744774357735174102373548473 + d *
    (-4764146428051688764316347821112 + d * (967156561592718306656691087362 + d *
    (-174359388097376050675905922876 + d * (26817706497513220806701929343 + d *
    (-3296693370015817067311776498 + d * (280950902437106237399877392 + d *
    (-8495066052714702897094363 + d * (-1437113177383537586489531 + d *
    (154918135617239914679589 + d * (9767798054536684029351))))))))))) + d ^ 12 *
    (-92613445668799206917 + d * (-1386614194246954002926 + d * (393216543184124085774 + d *
    (-52906815685227596257 + d * (3036881793039271992 + d * (134567576139309858 + d *
    (-30999910243363706 + d * (1073986606028396 + d * (13370307789416 + d * (11767755224919 + d
    * (-551443300455 + d * (-172312826007))))))))))) + d ^ 12 * (5104119907 + d * (1235031812 +
    d * (58452283 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_30 (d : ℚ) :
    orderSevenSelectionPolynomial d 30 = selectionExpandedAt30 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 30 =
      selectionNumeratorAt30 d := by
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
      selectionNumeratorAt30
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 30 =
      selectionDenominatorAt30 d := by
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
      selectionDenominatorAt30
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt30 selectionDenominatorAt30 selectionExpandedAt30
  ring

private theorem selection_cofactor_eval_at_30 (d : ℚ) :
    (selectionCofactor d).eval 30 = selectionCofactorAt30 d := by
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
    selectionCofactorAt30
  simp
  ring

private theorem selection_factor_at_30 (d : ℚ) :
    selectionExpandedAt30 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 30 *
        selectionCofactorAt30 d := by
  unfold selectionExpandedAt30 orderSevenDualKernelPolynomial selectionCofactorAt30
  ring

theorem selectionEvalAt30 (d : ℚ) :
    Internal.SelectionEvalCertificate d 30 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_30, selection_cofactor_eval_at_30,
    selection_factor_at_30]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 30 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt30 d
#print axioms solution
