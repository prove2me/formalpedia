-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_32
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:49:26.65286+00:00
-- url     : https://prove2.me/submissions/96ec72bd-2571-47fa-9493-75fef1e7e8a5

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval6.At32. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 32

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt32 (d : ℚ) : ℚ :=
  -2055156891355556347904 + d * (-187458864636758065152 + d * (229013366814384586752 + d *
    (-509461789263558025280 + d * (937951202162153947008 + d * (-628099008638907652608 + d *
    (115828078962039253824 + d * (113902789971613574784 + d * (-191472476794191936000 + d *
    (226358691825065691712 + d * (-167398841755278340800 + d * (90337924162791239616)))))))))))
    + d ^ 12 * (-41929829536774170688 + d * (11624783569635571392 + d * (8254961794058312448 + d
    * (-15276232169366812224 + d * (14052904472931715968 + d * (-10676219847607269696 + d *
    (7244662213216006528 + d * (-4354216951049719680 + d * (2383739417755518528 + d *
    (-1244890311697355712 + d * (610820371215503616 + d * (-268892382831982080))))))))))) + d ^
    12 * (107262386778513984 + d * (-41676410062706112 + d * (15965679185495424 + d *
    (-5418766392748736 + d * (1486892445534720 + d * (-364778241874752 + d * (112863090367680 +
    d * (-40882641356544 + d * (11276470588032 + d * (-1914959463168 + d * (280202937984 + d *
    (-108328054272))))))))))) + d ^ 12 * (40180560384 + d * (-6874848960 + d * (300271680 + d *
    (-33680320 + d * (50978880 + d * (-10562496 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt32 (d : ℚ) : ℚ :=
  -2435693045469853777920 + d * (-234244497204496564224 + d * (365728641365200338944 + d *
    (-837896012761947734016 + d * (1484221175436293511168 + d * (-1177918224592318721024 + d *
    (515553227068474034176 + d * (-175874096736824250368 + d * (11823300655023179264 + d *
    (147833181443116590592 + d * (-180758362896325474432 + d * (135349977036328034880)))))))))))
    + d ^ 12 * (-88433858802826480512 + d * (49891686267729420160 + d * (-17555990378924645632 +
    d * (513449565890472000 + d * (3806758235622107584 + d * (-3717172041985195072 + d *
    (2812810932328265792 + d * (-1767672415969807680 + d * (978072596417028096 + d *
    (-545755517595265472 + d * (304578564936734336 + d * (-154228248715320960))))))))))) + d ^
    12 * (71861641138259904 + d * (-34088034223063744 + d * (16493805879075968 + d *
    (-7481393390771840 + d * (3135458876541376 + d * (-1278428886919232 + d * (509252874224832 +
    d * (-187169822595392 + d * (62279220409920 + d * (-19675112253824 + d * (6042417928064 + d
    * (-1651145035776))))))))))) + d ^ 12 * (346363999744 + d * (-45942233600 + d * (1968546816
    + d * (405288960 + d * (-50566144 + d * (-1328128 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt32 (d : ℚ) : ℚ :=
  1791917198433636259424980539883529879749622926157583968060309504 + d *
    (-83476937524037668065837437974155322719376484228724317301229223936 + d *
    (50856078192362538727819878304306841448732490544257832116190969856 + d *
    (68562740462432806556559881922970392910447226891733484099761864704 + d *
    (-118728156606810672723407410796207380969182231810219206321226383360 + d *
    (197056132718079947827066664687258739145148532025686379096275156992 + d *
    (-159754048324403022878096819180355788951756532819506489346465202176 + d *
    (-20288880011513522275500904502500349993213270770124075186813665280 + d *
    (185989301911080455732715704540886016296913877058601802137256067072 + d *
    (-271657180915155319711817693481674008334258057359744993129720971264 + d *
    (260805974393484064457827583477429565237258555904117227644330442752 + d *
    (-135379300277633402505358215624714118306931588463758136026613678080))))))))))) + d ^ 12 *
    (-40643632019473482098494574586658484645731150890378509681322098688 + d *
    (173267166497668734074989549659124441973378181166141650038509797376 + d *
    (-225519567319515964962731441731973032274257972457029731691803443200 + d *
    (195959936304913778046738823034823438732774957852446048033099218944 + d *
    (-104974336965873529382270333977680327573425102275142659508781449216 + d *
    (-2736052559453738748925609820592096554975618423050944941618364416 + d *
    (85867409959884877026744129464727455056543466830759160703049793536 + d *
    (-126540747240805479374306435718843807657271257851893714887732101120 + d *
    (125012754694177188506231930630608620365042113396209316896351191040 + d *
    (-93149811151111627935453598583832749238734268739808707188788297728 + d *
    (49177534953588091104954443749627247894284090955373528346395148288 + d *
    (-9013281394848451808296739961996201372559678712510151597665812480))))))))))) + d ^ 12 *
    (-18687305432110079517113741738628060432213201603911509538316746752 + d *
    (31834776749352575896335120139532177638699591835711142177381548032 + d *
    (-32836389318695211123448242391542032341892341676028982332348432384 + d *
    (26404033420265907341204412491769919379749717985542246604458164224 + d *
    (-17230848396352536763927538489617868208208301327983214511710535680 + d *
    (8605000590736658217826216899268849865166911288790480673981071360 + d *
    (-2203900736023140980448944406206178467759272458185424772027383808 + d *
    (-1584245869715844901151073664299368439929840336718129572447518720 + d *
    (3182899802158985245121461629901608476674009591040442060887293952 + d *
    (-3329950346947891921165165646930133809768981343157949797378293760 + d *
    (2727166719719099185908952892284561679076427469004209621201584128 + d *
    (-1888586761790976874272173626001946827101886241707012382135418880))))))))))) + d ^ 12 *
    (1116389884598176399019426881550292922569129991731900606249172992 + d *
    (-538301501240451170699025947396014048449370201035410279056539648 + d *
    (169855339748339562671946384295744907960775633900724071856340992 + d *
    (27660674205059587878904883105582765815253418897873423280111616 + d *
    (-108474606085035092775914210892808970197344739837388376377393152 + d *
    (121708848029182482985611687424570332094369774408364413266952192 + d *
    (-103204586793569175102912985489467474038683985869743053938884608 + d *
    (75028012749281660563454527912643026187106651713860666159267840 + d *
    (-48548866798853992503710701369379534977344668250066894112161792 + d *
    (28170458920210838959496016935311750387929693903035254966845440 + d *
    (-14426752465132585806513357185960126702024305696421801298755584 + d *
    (6140804856785205137244461795465861552432605575766624559955968))))))))))) + d ^ 12 *
    (-1699150077504932371388922679307412056971146130381181994139648 + d *
    (-339476214079781005212066897960978092454100566010515079561216 + d *
    (1040126901900630827653025830804022868031615012448690254643200 + d *
    (-1092190948155913757601561683309840687307128085060090633388032 + d *
    (892165221819326948854369606551265053281859397468940373065728 + d *
    (-640603157011819321979323652081189412367614898290410453467136 + d *
    (422023018805696444028432230942581763730014460686150706397184 + d *
    (-260120700181028447073705938339206723717238455700077239074816 + d *
    (151457369838175364486454391456995944573533060179099873705984 + d *
    (-83654116047246941981376410993987357884541120575301740658688 + d *
    (43835842385696911887930889889100164567359387835940159619072 + d *
    (-21705046938665160924632187373926226609732362708458905796608))))))))))) + d ^ 12 *
    (10052143249219074937412121458726851802783101160491654840320 + d *
    (-4259577758197531740468592170970122246690179145284503732224 + d *
    (1567546773160545399913286806895773863939105072561740840960 + d *
    (-422538759315031024006907352729848263481139462519597039616 + d *
    (-1214744741033426250764559832434832013676244554145857536 + d *
    (117171502026667342942367001604940116365936266412424429568 + d *
    (-118669191242658368986907964737103387195943651178333077504 + d *
    (88465550419935343002099540037195225302868098458904428544 + d *
    (-57454588947497158062067863144860782513492939467076141056 + d *
    (34271380065615061141304657610399019757017026304662044672 + d *
    (-19219311347248190952386283866596300532172230455734829056 + d *
    (10257968670443163975776974136297358574635585184819838976))))))))))) + d ^ 12 *
    (-5247741934296070582451411166270182879400832448556695552 + d *
    (2584205411235560745790242284017438976194273836208226304 + d *
    (-1228136081791438663296901053667035920885604793372377088 + d *
    (564112278561304889727514562930619203924037411458514944 + d *
    (-250584942568682446370591773925937403014765172382760960 + d *
    (107636706077696523433603399257076407640038537847111680 + d *
    (-44666935517672568684522204322971671176266302759108608 + d *
    (17874579639953668148052666375867968949002395891007488 + d *
    (-6876708781941050226033099974413370054272113965531136 + d *
    (2530888955836094546448026437717645406702050017542144 + d *
    (-883774089419073307360000304037963102945262240006144 + d *
    (288567072487842787651792152596224112773836472057856))))))))))) + d ^ 12 *
    (-85588901194015642701718858460552463595895963516928 + d *
    (21493163320361516911379536591574616150228704952320 + d *
    (-3491396076738589936153441613603578700603828994048 + d *
    (-528562009783022206451768298104310741968408543232 + d *
    (892702135077878624814861243919271910807233101824 + d *
    (-581282315615163128534578719223790439213733511168 + d *
    (299662299583616677607102812684281038173116563456 + d *
    (-137235241419872466962536503013647847716209819648 + d *
    (58160050233069876288775107839828758088992686080 + d *
    (-23246593834155504416189299415309643758797324288 + d *
    (8852858247942071562323508792012882814208835584 + d *
    (-3231044567578799391689337061932447567440248832))))))))))) + d ^ 12 *
    (1134028013135786191951013773920693013206532096 + d *
    (-383455111877807635067486292562518059324276736 + d *
    (124995908249703795016021384696234300275163136 + d *
    (-39271291026222943977849733343606822838206464 + d *
    (11881916184565840262388949731223978783277056 + d *
    (-3457163663483887878567313697278558240505856 + d *
    (965301027773904700823949812551702948610048 + d *
    (-257858628683669168770113245915402821435392 + d *
    (65615158237858359235702395222550369796096 + d * (-15812851080439782651364928030293525790720
    + d * (3581412400674617086357122983203053764608 + d *
    (-754350016741134276765572284819107217408))))))))))) + d ^ 12 *
    (145544849037405510380247557476310843392 + d * (-25133679360982827183036429893136285696 + d
    * (3737013732129152798003078196569309184 + d * (-443187831403125464663021481838247936 + d *
    (33534430200992681679201118396088320 + d * (546013016446703413082806016278528 + d *
    (-633518632815814309437280802308096 + d * (98414674632987969802330155515904 + d *
    (-6648781576059873567599049310208 + d * (76452024941730355238347472896 + d *
    (-96510106413717428005363515392 + d * (47972151994885413979790770176))))))))))) + d ^ 12 *
    (-9244098879365710827648974848 + d * (771617638288169738612244480 + d *
    (31860265427350713263456256 + d * (-14977074439539134729551872 + d *
    (1373716802510646761750528 + d * (-3950448239422723325952 + d * (-6903271533327864823808 + d
    * (127171491867525906432 + d * (11520029519925477376 + d * (5086561097457860608 + d *
    (-293592136044511232 + d * (-55010686430347264))))))))))) + d ^ 12 * (1621030710804480 + d *
    (345291001430016 + d * (16128781058048 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt32 (d : ℚ) : ℚ :=
  28022077983623651893129481793711235639750721030586368 + d *
    (-1302763826731031089293525692164757448437219399663878144 + d *
    (666761798368910089430629721249050054310822999155015680 + d *
    (1382382255098761175979272445999220690765935171394863104 + d *
    (-2034801808186486098516761547850347116051434736694853632 + d *
    (2764257564655167231051824818209979665604622638355841024 + d *
    (-1634356892603314681502072402660974063215285061323587584 + d *
    (-1373916192543516319956362793791361183089973602780446720 + d *
    (3512036076093797168685129794750208197035563517653319680 + d *
    (-3875185454964528272463642869377990930200690951328042847 + d *
    (2754272487269421804975014892058279223159379003638473562 + d *
    (-450307208053156504722683909119256162932389858968520727))))))))))) + d ^ 12 *
    (-1863654149968642519382115852936054193135986797668122117 + d *
    (2984030604040912238515840063978535617497516620551199366 + d *
    (-2813297892843550961324702053070917149408063661298956437 + d *
    (1768855009308151189791621587127447291974134059170787818 + d *
    (-348715500960373199932843070535203391615425439334491370 + d *
    (-870505843641356000392713100380790787119987040767754660 + d *
    (1520587749987419438983753064560053011962255064977764068 + d *
    (-1590215117573607485772078412503297503446559554533813924 + d *
    (1249175124664954821897809679384134227181174297306259420 + d *
    (-714809193325846120841673980153407995035095051747860927 + d *
    (197787230139942215783878193362719345299109705496339664 + d *
    (169033290295623933778920192640336551304792300318650056))))))))))) + d ^ 12 *
    (-353326063817694182207706495313838410712654213071823983 + d *
    (385349771411022298280538423063760078464366664862759526 + d *
    (-320526173970195315268580929352327583344110237936245947 + d *
    (216428080151194452125056942156933938535442883715505470 + d *
    (-115425417947129724880276204289213821313035141351196193 + d *
    (38776977250005138380870192126668419254267586297419023 + d *
    (8413088542550073703471734205523516526351648474833947 + d *
    (-30265571949009839192204203345079779350943285775200392 + d *
    (34800409547769998323780524922902886596791615531622255 + d *
    (-30010654319397002954448826230613336448589714923925831 + d *
    (21800175065775120208299168299003691442255090848140656 + d *
    (-13690244144629036189838241407201999349126229900971191))))))))))) + d ^ 12 *
    (7308593754814400134910440341179752603534386774464540 + d *
    (-3024286759479380298800221967452205270016700340852283 + d *
    (545464067467545356020513092197599569226386347313188 + d *
    (639539916029465948987913424753818382521880909867565 + d *
    (-1023955161942196007262652605854448426911714718694466 + d *
    (988344334851223817353483895969260646793078782998831 + d *
    (-782658478970798596582573611609851892637813153841905 + d *
    (546985648567913506626456556713639935270605213794201 + d *
    (-345711957964110568545022284250225806100606372058811 + d *
    (198391800638570624028269285141155632766541413367163 + d *
    (-101934896981966691487339603769007946543137959147243 + d *
    (44675146075434209308317409726791297409171232936587))))))))))) + d ^ 12 *
    (-14017801914826605746102523431755576364428049541249 + d *
    (-343401294657482959362013543017084776214299149193 + d *
    (5678829703075460948439287501216248607484149282266 + d *
    (-6576139564436352110377243796235443263736499157403 + d *
    (5649178632260188249656620765250848965342243412323 + d *
    (-4232883070247150666523411105810612397122744376540 + d *
    (2915207692883435221188050616032331962609510462443 + d *
    (-1889967489595492491072343930849500239138715396920 + d *
    (1168416881421324359628521806175488627302877761225 + d *
    (-694161045172530485355847411689884496127777041194 + d *
    (398295295794083876641543429121739490274693276959 + d *
    (-221451456608514872575673563611580348828790108255))))))))))) + d ^ 12 *
    (119576907106846906759082092273576753968530357028 + d *
    (-62799057890868121002080393418854052191828493435 + d *
    (32108328843379782646425604709551256571323558684 + d *
    (-15991712443752438578090285184891471619985440183 + d *
    (7760523142027204767812022776826014302811678354 + d *
    (-3669297896772514803566783125224499638484592069 + d *
    (1689801011015471195359305377680056315922165533 + d *
    (-757521699056218304007285031824069664392006095 + d *
    (330266682453326201913816379413796708774551465 + d *
    (-139854849788119593093917343793590098051319290 + d *
    (57418588968398308466338506938522527194872977 + d *
    (-22797794748114576597696317844436797924413532))))))))))) + d ^ 12 *
    (8721492297654787944725860244164096678252506 + d *
    (-3196720242503188126339304345760175773326929 + d *
    (1112648394568062459764849826020392782894425 + d *
    (-362133977257253466220639424430154695428734 + d *
    (106916673226302736946694282269115481420170 + d *
    (-26567421357729929793702282632082265483343 + d * (4117074881022394299050617733854392884132
    + d * (819522891469048319311662077031531277042 + d *
    (-1205691163170883335210385324166307744436 + d * (773077495493979391055048518946430548131 +
    d * (-397047442493634623163025271893014672523 + d *
    (181830116229917357790864560282580962533))))))))))) + d ^ 12 *
    (-77194064246878974527362291687310146736 + d * (30939293487854018951465078972057238758 + d *
    (-11820840821449199059577001183671570470 + d * (4328800526772555955518148743058032156 + d *
    (-1524182880563299594955445361390300122 + d * (516934348575341453072793810171063621 + d *
    (-169006650418659784685728365702134184 + d * (53250705139942781424132058772353172 + d *
    (-16146367339096250371735854448216609 + d * (4700025920669592709264083573362796 + d *
    (-1309612635878447799611876836268413 + d * (348226006124389743228691985979607))))))))))) + d
    ^ 12 * (-88010437758171507964501752999858 + d * (21000504833890367078506118614303 + d *
    (-4674369956275441808332008467618 + d * (951935279985298143978920454758 + d *
    (-172417459224652442308844571950 + d * (26659872861626425169197500163 + d *
    (-3292556042644626573719179410 + d * (280697899523957902682906924 + d *
    (-8047291200607761925379445 + d * (-1575288633040476769531741 + d *
    (175545899441633083083605 + d * (8558059375016595844181))))))))))) + d ^ 12 *
    (-214097445536271418765 + d * (-1357883280211890170862 + d * (391610775640167902934 + d *
    (-52976423601243095033 + d * (3040809813541910754 + d * (135705018203579826 + d *
    (-30983494467031296 + d * (1056271488401968 + d * (13182120729120 + d * (11888333135601 + d
    * (-543402222453 + d * (-172010450003))))))))))) + d ^ 12 * (5113013863 + d * (1235133412 +
    d * (58452337 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_32 (d : ℚ) :
    orderSevenSelectionPolynomial d 32 = selectionExpandedAt32 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 32 =
      selectionNumeratorAt32 d := by
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
      selectionNumeratorAt32
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 32 =
      selectionDenominatorAt32 d := by
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
      selectionDenominatorAt32
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt32 selectionDenominatorAt32 selectionExpandedAt32
  ring

private theorem selection_cofactor_eval_at_32 (d : ℚ) :
    (selectionCofactor d).eval 32 = selectionCofactorAt32 d := by
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
    selectionCofactorAt32
  simp
  ring

private theorem selection_factor_at_32 (d : ℚ) :
    selectionExpandedAt32 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 32 *
        selectionCofactorAt32 d := by
  unfold selectionExpandedAt32 orderSevenDualKernelPolynomial selectionCofactorAt32
  ring

theorem selectionEvalAt32 (d : ℚ) :
    Internal.SelectionEvalCertificate d 32 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_32, selection_cofactor_eval_at_32,
    selection_factor_at_32]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 32 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt32 d
#print axioms solution
