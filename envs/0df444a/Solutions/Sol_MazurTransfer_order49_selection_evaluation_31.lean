-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_31
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:43:20.698855+00:00
-- url     : https://prove2.me/submissions/e9ae6ce0-a5ad-4718-8746-f823656f9a5c

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval6.At31. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 31

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt31 (d : ℚ) : ℚ :=
  -1405460936492720759296 + d * (-133680080353954763520 + d * (171418077196930977408 + d *
    (-380748608146251396672 + d * (686966461014192701184 + d * (-459182083825478736000 + d *
    (80143248711112675776 + d * (95409592994751391296 + d * (-156982297963273148736 + d *
    (182066819597973036736 + d * (-134380552510326537792 + d * (72468453185286248448)))))))))))
    + d ^ 12 * (-32782043829271879104 + d * (7739560500160849728 + d * (8423020960266423168 + d
    * (-13959356010547610112 + d * (12710627132376861312 + d * (-9651439003997089152 + d *
    (6554557376352223360 + d * (-3955768631129530176 + d * (2179499909050052352 + d *
    (-1143639842183977344 + d * (563141241962587584 + d * (-249340713673945536))))))))))) + d ^
    12 * (100275532937063616 + d * (-39179934545500224 + d * (15021162812563008 + d *
    (-5104677184932032 + d * (1410556630987584 + d * (-350366830631232 + d * (108811170577344 +
    d * (-39262841191872 + d * (10847180828352 + d * (-1864404950592 + d * (278453193024 + d *
    (-106561937472))))))))))) + d ^ 12 * (39312747840 + d * (-6767866176 + d * (306739008 + d *
    (-35829952 + d * (50836032 + d * (-10564800 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt31 (d : ℚ) : ℚ :=
  -1665696196122273000000 + d * (-167240696874611848000 + d * (272163548891316383488 + d *
    (-623497824530916999168 + d * (1090909155987868503104 + d * (-869645041825488920128 + d *
    (382258974752594623104 + d * (-124777718937806042752 + d * (-3457641862267999104 + d *
    (124627549588331079616 + d * (-148107414050795161472 + d * (111001072419601727232)))))))))))
    + d ^ 12 * (-72410773650392587328 + d * (40397888642862805696 + d * (-13795124904743928192 +
    d * (-170076202934590336 + d * (3675403526023048256 + d * (-3494209169026416256 + d *
    (2613662924467093888 + d * (-1639331511844603136 + d * (913904287970617856 + d *
    (-512550511393896576 + d * (286425680674113536 + d * (-145977049587339776))))))))))) + d ^
    12 * (68865255442156096 + d * (-32958901294944576 + d * (15994913622465536 + d *
    (-7289582706750720 + d * (3081762418674880 + d * (-1265532539358912 + d * (505506034770816 +
    d * (-186335532016000 + d * (62386119270720 + d * (-19827664692608 + d * (6091269340544 + d
    * (-1657937785856))))))))))) + d ^ 12 * (346419788800 + d * (-45872790016 + d * (1970110464
    + d * (403898368 + d * (-50706432 + d * (-1329152 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt31 (d : ℚ) : ℚ :=
  573077569070797233389865935431500811257895534997635263671566336 + d *
    (-26682985182313192668681000151679543618495690491788315187331727360 + d *
    (15834552120165870412774493678659401958033594211114938758638600192 + d *
    (23450780557873951060684893977066166845739141554983575996626108416 + d *
    (-41185391501160591095498265768774920809613529174653457807215689728 + d *
    (67386084911344691442875360295581176300057959561021873534408589312 + d *
    (-53086897740105938487620704130331903982760505578177883702812213248 + d *
    (-10840987725361952726609587866553098616477460491586236763063975936 + d *
    (70497391533422660860536690102310836567781427340029438841595887616 + d *
    (-101325820209019247450095840357701978189224637063890636124080046080 + d *
    (95530074537657169311273154821118125129309264194389345132118278144 + d *
    (-46670812146613807898132722327407896392928182617653585055195594752))))))))))) + d ^ 12 *
    (-21079361407965064324000304371808588897255483518603883499037917184 + d *
    (72164113366336161508000400446488560113061734026570070479224963072 + d *
    (-91456393806600638807596573529669506948661821972253123354821132288 + d *
    (77743576765882177293661591063454359624618243916515703424375848960 + d *
    (-39320223253364161200615321405044721817731055662820805107525877760 + d *
    (-5640133021947440655398353391981150703689176728488309053554688000 + d *
    (40163191944705870719186058761558009652367411948986090488206458880 + d *
    (-56553600282352777658394927107021059676162235334901428053196406784 + d *
    (54766394188023318381263527946712997379429848031438727399067877376 + d *
    (-39923004981645648967036611506569557916426094487825534235923185664 + d *
    (19954593421786183869050641655053139558136117796219564780115722240 + d *
    (-1861458496467222902105840986301447864046876713365258812937994240))))))))))) + d ^ 12 *
    (-10467225636181540397867966713019336184392620753551528186478592000 + d *
    (16075492141519708236298557118361817893000691674377355894638247936 + d *
    (-16081952831306532662452956740822602787826411442846700026922270720 + d *
    (12678715924545800668761223784806985806681957479342291964066791424 + d *
    (-8064162847877766998883416738952198085134168820320110560873283584 + d *
    (3794701842529482481766738756820658297763763860248474862124007424 + d *
    (-666772865719416851681737782142439794712031484674990974909546496 + d *
    (-1144842035178089652090226728835985770182471075977545896965701632 + d *
    (1860155409134608171943165675472333768672776547779857463679909888 + d *
    (-1853351248228790573099955663077444070642960789076533500960309248 + d *
    (1480894073351803046161847119891669105290610120449471429203984384 + d *
    (-1004442997992594626351560274607116136444078694672279320275714048))))))))))) + d ^ 12 *
    (577142792519146466848597727231735765772451431126264567715856384 + d *
    (-262226197420087731244882079332502873031317773143383308688687104 + d *
    (64875234024826818874745670086653986620421113802644004642750464 + d *
    (37829330818991714383425491428039956260378315349309035623743488 + d *
    (-76575889083506981643033624677505399440618011737711753113894912 + d *
    (78847884196572756544483886519986524655881449609540387050618880 + d *
    (-64585670900464052320531688000785794505721417961966315550015488 + d *
    (45986814421850543158691955308757108245350642320054664678342656 + d *
    (-29237846508408202992536931955034328585922280000459152637296640 + d *
    (16610999531884535469780444057450372329176518353325618171478016 + d *
    (-8217405421022559155095418463970274652682360945800728638390272 + d *
    (3232562514589996683562840290728166336934506714800129034420224))))))))))) + d ^ 12 *
    (-619667677106703665692117715646380295472761743388235193384960 + d *
    (-526411196671407996606230761761546301688776019390645865021440 + d *
    (867531549999104716951791957788696907791737178193424838557696 + d *
    (-828944318617542052519989366717324254130350215240610101329920 + d *
    (653095643048370272351644630575907904783002284276555542691840 + d *
    (-460642923014255220854132209802545026686224373866164125171712 + d *
    (300430527102989387910419974006916054401911551953207334273024 + d *
    (-183999686098598057080557262289167383438736070491824270606336 + d *
    (106622366214333237062287152988907653728154833303876201349120 + d *
    (-58615679048867339617051781713723594691535427755038882136064 + d *
    (30533033145737811687095654338131643684300895216393536667648 + d *
    (-14980931746271231530091419041285518615345672896561733697536))))))))))) + d ^ 12 *
    (6830106837093876133237525759346274725076914072209190289408 + d *
    (-2808560026886086033045346874220849188442214429492518060032 + d *
    (964328975988707774136078717879642788174768366543923838976 + d *
    (-200132754875834086335183132673249618198542108640080560128 + d *
    (-66074819648801054542508914711067909928420330703290892288 + d *
    (124484707583523338814477788554651702785141738187980537856 + d *
    (-109588153178254881665583427591143208610655507102625955840 + d *
    (77865889621585152480909490370634513227054393874152947712 + d *
    (-49461709298376402166037451570741407725192086522994098176 + d *
    (29170624249393099915603635774225076873041957019391361024 + d *
    (-16263482478080537744550582127897409700565435404921864192 + d *
    (8656885538017720809817176924206329250496958970015252480))))))))))) + d ^ 12 *
    (-4425127096744230631308541962503178489542343646177918976 + d *
    (2179974207038541566283709848290478534931922760791752704 + d *
    (-1037198965284338349714844612949116995604989080712511488 + d *
    (477146700588341548901038779296286969858765984363446272 + d *
    (-212313468018554378152545206169602456246789628465250304 + d *
    (91343798224794986642924763087494473718531414307110912 + d *
    (-37953247190345512081795073927056024874094210316238848 + d *
    (15196774054805962518833850233154742205064178321063936 + d *
    (-5843265650686207857772113740353201296517261100843008 + d *
    (2145286454995972937558976269876722911575095734435840 + d *
    (-744855018188331596874533073719682771559601356144640 + d *
    (240343886393979314800562736648009477227174933561344))))))))))) + d ^ 12 *
    (-69508116284795726606933305780381897318895486763008 + d *
    (16364184620408379059700002589895477115014525747200 + d *
    (-1936690848517988691958051776635759972073632169984 + d *
    (-971961084168133141529385749627000928875071930368 + d *
    (1009652153137270411174500756544946656312850382848 + d *
    (-608870982770184442208070639392067550746110066688 + d *
    (305026976744557484173760501311717523036242182144 + d *
    (-137850773430414692186679584512543639677884432384 + d *
    (58043775177759604090997006129290380563398000640 + d *
    (-23132520145666520949438112802078730182499500032 + d *
    (8801837932389892729280939278402335321745522688 + d *
    (-3213679213088519478787204631200300551504134144))))))))))) + d ^ 12 *
    (1129241353309719375335922199936632810319904768 + d *
    (-382455614707561666103359102864126648026923008 + d *
    (124905002765142568003341839976799903176196096 + d *
    (-39321784381260095284679271744261165028737024 + d *
    (11921461297273880177618528756620341148647424 + d *
    (-3475478042508790940319037007426384245555200 + d *
    (972145212049627268029613411570462693523456 + d *
    (-260079689689259752916664338971605504884736 + d *
    (66257626425373726086674461860538945110016 + d * (-15979710432789599281731115043749628477440
    + d * (3620112634711626843943037665026226257920 + d *
    (-762226579916643741110631288557287768064))))))))))) + d ^ 12 *
    (146906561677208482742700387235750215680 + d * (-25322238699727139420285161168655089664 + d
    * (3755408558383745207199786161433739264 + d * (-443960025514762653945999664002629632 + d *
    (33473522950841059062935361937211392 + d * (540990669577370068009121820966912 + d *
    (-626341603360686477536894813208576 + d * (96752794843637029958745654296576 + d *
    (-6491726194092447083111765508096 + d * (85283383464709192708204265472 + d *
    (-101084458360129836973282557952 + d * (48512801798800995203708616704))))))))))) + d ^ 12 *
    (-9254651410690632102042927104 + d * (767699422614062255976480768 + d *
    (32160190587488663385407488 + d * (-14964917166268989994434560 + d *
    (1373253153702070118514688 + d * (-4240962748081530732544 + d * (-6901429316279200907264 + d
    * (130549703420987572224 + d * (11538530794909728768 + d * (5067296899579510784 + d *
    (-294809934567047168 + d * (-55056771936944128))))))))))) + d ^ 12 * (1619712106561536 + d *
    (345276677881856 + d * (16128775815168 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt31 (d : ℚ) : ℚ :=
  9838113828537063207390954162414118911454816474793441 + d *
    (-457109639897105184119602326118048066012453084056546125 + d *
    (225268896491640540024808284957425128440622081708463781 + d *
    (514077133101209871893598047800168697436108782410711949 + d *
    (-766801217079497499847365940907561131437589669663171648 + d *
    (1029282500588760638501388748926597300237974501318706143 + d *
    (-577330224278189043532077127745662159267355977378650185 + d *
    (-588874868980318785330396406257824281552427222900810312 + d *
    (1426657274083885658217361436879371981907609920118347532 + d *
    (-1561669513102468105262972540990509297732875517331838078 + d *
    (1081082237541115585041373803091315557698976826229682030 + d *
    (-112370406922414172286682154420541250045208125868602171))))))))))) + d ^ 12 *
    (-854935691293288681771476179876942703869356220205558360 + d *
    (1318901254915068707610574152370982332624599036633044074 + d *
    (-1224941593308282004244355184414934406452212901424377177 + d *
    (744015992342110718889473134062069102219272951867268206 + d *
    (-98567808628171325630134166943176538287384677101781062 + d *
    (-452108456640360898928840863627518922682520150411105940 + d *
    (741201653402422907458197584846702512874131276032612073 + d *
    (-760230605352711832881092820664837117228596208696583823 + d *
    (586216679106273790063198549597303889751729587418680307 + d *
    (-322329767952029542606804057936010202956856641253763001 + d *
    (69401268221976068339036795446191393718763523820588655 + d *
    (108539962464076751550142208177762672062840910252514190))))))))))) + d ^ 12 *
    (-195362771672315517842136976236006203378123318687088872 + d *
    (205873731985153036964939290981010558721930152241993180 + d *
    (-168027201018887722675895326441149729785108964131413793 + d *
    (111093330868142744843343628570031907280068713330207681 + d *
    (-56735241968539204342771894586872594521299632716397993 + d *
    (15912307445918592061345973134797314190087378324849047 + d *
    (8799604180413689837612384231334415748668364086857130 + d *
    (-19729618548749426546946282760224329809365424517619079 + d *
    (21292047789274386028935003068911250751830992324797001 + d *
    (-17878644066899774947553427277036889055676204786070917 + d *
    (12745332279958065310909469705317055774348273866625336 + d *
    (-7834850053930780498037028975049677326395979273334724))))))))))) + d ^ 12 *
    (4031311043225058871901952263771195519066674267112526 + d *
    (-1511682717389053413893730427684747984563013636405780 + d *
    (82148490759257762509562769901270530288560866756773 + d *
    (572590606858249911523351142348175456038037430180820 + d *
    (-752868305501636737732509448452144627790458571339207 + d *
    (689234828799369937885492005468516351977312399067629 + d *
    (-532413004055143153800393886810722652596601353319279 + d *
    (366192903862077538386646136982109441743326721588383 + d *
    (-228187981123149179284231217226788608298333457521516 + d *
    (128666815934849356912831850581342240318319159495691 + d *
    (-64208389417085060457290265576486995619016803915149 + d *
    (26391024039666215359715297729515959538393659153997))))))))))) + d ^ 12 *
    (-6505962758787947200325463217692484593355756790878 + d *
    (-2477245827436100790881344282439572273405502321975 + d *
    (5487359149270110138545335620029668913711157176851 + d *
    (-5620961388110115319463115231120220652975666432178 + d *
    (4632630033057181364675723196738991582873919278351 + d *
    (-3408423529037419428973206694800523491580554252199 + d *
    (2327774923276197723768020262572581844876569988280 + d *
    (-1504141448365588296372821908126707970982597155546 + d *
    (929558228556887634403834573131603263364642109356 + d *
    (-553078330402817722390182253592138611975706722979 + d *
    (318203708243915234974647667986511052862945298188 + d *
    (-177543058983746625208295960240123153843254062305))))))))))) + d ^ 12 *
    (96257645210617022241775745546429214352087492483 + d *
    (-50776647811722148657704645020008621318223690636 + d *
    (26082755866087410903078975923335473630566383151 + d *
    (-13052999284575767745379987365506661335821607481 + d *
    (6365058721225168103169337765800707995266921571 + d *
    (-3023948380354972681196727303771765375502575418 + d *
    (1399130960833946551548491350135919551200752877 + d *
    (-630035377842660001729914688525480732291257757 + d *
    (275839570272137300051271829568791000806205090 + d *
    (-117250540057595320197113108805796239340112901 + d *
    (48293189075606869307252496209538071753006965 + d *
    (-19220429195446714648824563048233498147397873))))))))))) + d ^ 12 *
    (7361532757002810002838543318995081203839460 + d *
    (-2696327895443810304764859170379215199799870 + d *
    (934887586671372701933474622511826896789643 + d *
    (-301361346174575379882704705830917203618833 + d *
    (87010582666753189909134378330268621748512 + d * (-20363003386640947805050941112432985197357
    + d * (2297187597165401439250665023412941366510 + d *
    (1312366777183564470788886455892518674526 + d * (-1324328453730691762602472511335885334505 +
    d * (796083054339995020192300022987085981457 + d * (-399245781829121563390351197330593706251
    + d * (180918447580319667569069339044053681126))))))))))) + d ^ 12 *
    (-76450658167867978823767198498260634242 + d * (30593354102845004623118739636319734127 + d *
    (-11691040155948672466476584765235461694 + d * (4286747004828908105341262522777504837 + d *
    (-1512322087955411585690645336398912058 + d * (514116328082699937291273812875329385 + d *
    (-168509490177333687239132986394680528 + d * (53227947421469535533741797521110589 + d *
    (-16178444288024830963430719382902792 + d * (4720091147039875652677322577020136 + d *
    (-1317994823587649741885110555479383 + d * (351106086954448979825580207006950))))))))))) + d
    ^ 12 * (-88857653568210161650758608415413 + d * (21213492101004367219372427122116 + d *
    (-4719219666088322722116902961726 + d * (959558658023903857548442574345 + d *
    (-173393041757594114144911822876 + d * (26739516255171101491152594934 + d *
    (-3294663175195410151981161562 + d * (280816051271696186208636634 + d *
    (-8269131841665484630476299 + d * (-1506359049943167349666266 + d *
    (165226446875017881894810 + d * (9164451636225080264973))))))))))) + d ^ 12 *
    (-153329575281670885622 + d * (-1372261724574129808800 + d * (392412718569009466340 + d *
    (-52941443858289837159 + d * (3038855883329084719 + d * (135135155683663937 + d *
    (-30991820766566467 + d * (1065123839199620 + d * (13276059212711 + d * (11828042107139 + d
    * (-547422765937 + d * (-172161638005))))))))))) + d ^ 12 * (5108566885 + d * (1235082612 +
    d * (58452310 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_31 (d : ℚ) :
    orderSevenSelectionPolynomial d 31 = selectionExpandedAt31 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 31 =
      selectionNumeratorAt31 d := by
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
      selectionNumeratorAt31
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 31 =
      selectionDenominatorAt31 d := by
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
      selectionDenominatorAt31
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt31 selectionDenominatorAt31 selectionExpandedAt31
  ring

private theorem selection_cofactor_eval_at_31 (d : ℚ) :
    (selectionCofactor d).eval 31 = selectionCofactorAt31 d := by
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
    selectionCofactorAt31
  simp
  ring

private theorem selection_factor_at_31 (d : ℚ) :
    selectionExpandedAt31 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 31 *
        selectionCofactorAt31 d := by
  unfold selectionExpandedAt31 orderSevenDualKernelPolynomial selectionCofactorAt31
  ring

theorem selectionEvalAt31 (d : ℚ) :
    Internal.SelectionEvalCertificate d 31 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_31, selection_cofactor_eval_at_31,
    selection_factor_at_31]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 31 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt31 d
#print axioms solution
