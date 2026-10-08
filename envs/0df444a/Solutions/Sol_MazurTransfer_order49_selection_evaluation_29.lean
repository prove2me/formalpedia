-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_29
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:30:57.236906+00:00
-- url     : https://prove2.me/submissions/db666459-6883-49c2-865a-fb1ead51fb22

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval5.At29. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 29

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt29 (d : ℚ) : ℚ :=
  -632717682077913546752 + d * (-65762213059353440256 + d * (92861365835144603136 + d *
    (-205694626379150744384 + d * (357040920148543857792 + d * (-237431916908483479680 + d *
    (35374682994011696064 + d * (64793633643926872896 + d * (-102583259792905048128 + d *
    (115025517645193953472 + d * (-84569714150142007104 + d * (45367469464380454656))))))))))) +
    d ^ 12 * (-19174442957455053760 + d * (2382195421111271232 + d * (8111415649456973952 + d *
    (-11456304275370492672 + d * (10261437338292892800 + d * (-7795331792303532672 + d *
    (5311023876205825792 + d * (-3235579087219072320 + d * (1806754991124657792 + d *
    (-957806975581959552 + d * (475466185232045760 + d * (-213128744157117888))))))))))) + d ^
    12 * (87143553659769792 + d * (-34440601928452416 + d * (13233683455227072 + d *
    (-4511705866907072 + d * (1264933203585984 + d * (-322071932331840 + d * (100799436799680 +
    d * (-36113210697408 + d * (10014105242304 + d * (-1764148835136 + d * (274330162368 + d *
    (-102959121984))))))))))) + d ^ 12 * (37586122176 + d * (-6553700160 + d * (319673664 + d *
    (-40129216 + d * (50550336 + d * (-10569408 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt29 (d : ℚ) : ℚ :=
  -749869501091620718016 + d * (-82479955820387755968 + d * (145872970961372655488 + d *
    (-334280985395943557760 + d * (571498348169164688832 + d * (-459779010438011720768 + d *
    (203189903922182523136 + d * (-58767331721955946496 + d * (-17713433564768379904 + d *
    (85884771699432185152 + d * (-97239664760480957440 + d * (73027792191428707200))))))))))) +
    d ^ 12 * (-47440988402290279104 + d * (25796527327325291200 + d * (-8120748016710362368 + d
    * (-1082047379845623552 + d * (3327543616497647680 + d * (-3031703046236036992 + d *
    (2228263506579705728 + d * (-1396935014405994240 + d * (791231813473506048 + d *
    (-448689016496655488 + d * (251886418777723136 + d * (-130224587942400768))))))))))) + d ^
    12 * (62979195879575232 + d * (-30688703952837568 + d * (15002109470607488 + d *
    (-6910049932204928 + d * (2972997806950720 + d * (-1238342604294080 + d * (497724785048832 +
    d * (-184699792818176 + d * (62621990935872 + d * (-20134696476032 + d * (6188633959808 + d
    * (-1671475058688))))))))))) + d ^ 12 * (346539175936 + d * (-45733798400 + d * (1973237760
    + d * (401117184 + d * (-50987008 + d * (-1331200 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt29 (d : ℚ) : ℚ :=
  52278963630803472470696170057534207612207313544024906106929152 + d *
    (-2431224718084159296137860248065091879172541140768378974113890304 + d *
    (1355049776270317109276503054416477339267471392677097207390797824 + d *
    (2463045635908014639479424858297124875323826236479586211825975296 + d *
    (-4441688713418914981211267815879735107489545117367214900765786112 + d *
    (7053678342412726724139287635922315457756078905058153564528705536 + d *
    (-5179434600932579392202934166281782753254098039908741112058871808 + d *
    (-2124953906992031773455341381139405498382821500709737567303499776 + d *
    (9124377665768746087519390757515889003116352942433236567164452864 + d *
    (-12703421970766288631600306235501210840657206886604552387881861120 + d *
    (11489093936374588777505698334377000798303435507596289996307824640 + d *
    (-4731597511509312771719971712620620250733439703837282252388827136))))))))))) + d ^ 12 *
    (-4427222090270937083162770197158447611666373885881965172154695680 + d *
    (11318261753906709957209379213565853067209058548574552930199011328 + d *
    (-13633097967257710234583749584101495561183868253625031173860753408 + d *
    (11019337813620106059598377007858544822374040807978487090275942400 + d *
    (-4730875321282490448872315318872331511780288724031280895924109312 + d *
    (-2467298407551646448082337997467523214859581943046473058357608448 + d *
    (7921237127278003953719529024954936406495807973308783212142526464 + d *
    (-10314357854556866014363802041476718970201743313668551524651368448 + d *
    (9588405332412818788416959739171993013121172370187480793794740224 + d *
    (-6623677798632609772474890260850556423373225980093209710242299904 + d *
    (2813300179732160882990912782657745855095412918973293162849370112 + d *
    (581533122387099853263580789574733823568080531320794052002840576))))))))))) + d ^ 12 *
    (-2828707783537718297191044938467320076604944150343501761151500288 + d *
    (3741133302843302146346461821296306111588979141979052025966493696 + d *
    (-3542727700712983687420223733395384352792298316535312794397179904 + d *
    (2676245816874175149326500281254870225798465407743268315901984768 + d *
    (-1593450704043743683621456498303397923407461628408903128619155456 + d *
    (621445864853506968295607039197450722133430172672114618012008448 + d *
    (71080511968891931999353605146860813043789014682214606971863040 + d *
    (-451053228825232651668754538318158544581765157509693044119830528 + d *
    (573480061405112671374601236814935979197145059615885563243528192 + d *
    (-528667981606914772206598413225632230278248294421042512018538496 + d *
    (403167174353344340032734483799659082949455466010326824909012992 + d *
    (-260868752076973184796285760211793208104049662918482453890334720))))))))))) + d ^ 12 *
    (138876423229625145804293491382540234018084712000969618793955328 + d *
    (-51732755696106769417430326421314351913290414541016259770187776 + d *
    (-760032650527217216858352229258635385072070616201480287289344 + d *
    (25975354043025651218629988958133177805799181530206920132788224 + d *
    (-33141034250926471337956513547409021433095190604770327536861184 + d *
    (30378228073273655132358401363578133895015976729357380687757312 + d *
    (-23525831046485379892577263281941984465121882553313264647012352 + d *
    (16108567536297791348655951121598046628197726119793751738286080 + d *
    (-9849466764791254532508070566626586345749149121338014847991808 + d *
    (5296655496591226975708802923919221866771035587220664367972352 + d *
    (-2356771481180092030500521457226627586077811361188510986141696 + d *
    (671339462128528080137279919775331453193216519107917250035712))))))))))) + d ^ 12 *
    (160368402821380598540451249366725581331553626753974191521792 + d *
    (-476010605503938778123757230677333257194684011734602386767872 + d *
    (518258890925279558314184162349410986458755176626308367253504 + d *
    (-440898363945665580288053592334333713946933569297627004796928 + d *
    (329926716899558252997733023031771659467884883360474922483712 + d *
    (-226451684075816733044456361685651405058006714569121933557760 + d *
    (145324135321002206011042936890648422229351970479271003553792 + d *
    (-88026509957661905541749663885919029390691840801749051899904 + d *
    (50527808960391175926250264092044257537581423077841481236480 + d *
    (-27479640891357147982502007172525945353398806222517047394304 + d *
    (14094326245824118693446282557425564847041934605767659487232 + d *
    (-6740619591681713663307136878642394538887941372291582263296))))))))))) + d ^ 12 *
    (2932128899468995183142127339878642764632730704037200003072 + d *
    (-1091276570099246502888283481085763810444320397742597210112 + d *
    (279207698538089961621996026073919848395136453274876510208 + d *
    (30563635562227072231584906859424828417236090378397155328 + d *
    (-115893165959548568080998660224853181538495717781554069504 + d *
    (113745986401953476159119693732739522242742079787365564416 + d *
    (-86051854810026106006306781460396219292685658608374644736 + d *
    (57410880364138750714925447547683714096947671475241091072 + d *
    (-35355192970086058519558106605061964639919862698401595392 + d *
    (20521979461513851759733706600604300627823388191605653504 + d *
    (-11354029925621724009816123102881890475327928559000092672 + d *
    (6026750164522726904645897286235742441568097695760121856))))))))))) + d ^ 12 *
    (-3081414557838922483584348639689172552472647945904455680 + d *
    (1521261458917375765791660408852416043927307056324280320 + d *
    (-726167045479111039908190469683874212838377950585290752 + d *
    (335345156079152771904949463524471512826768849087496192 + d *
    (-149799495807177939658906946212235560863576560376741888 + d *
    (64671951683299777832281679607071105526888186445824000 + d *
    (-26937291667881417788343562323266983280459351859920896 + d *
    (10793403333133381785049463178718936080773537039908864 + d *
    (-4140894472101787519116801999777187148345474775515136 + d *
    (1509461507318508079853284566283951722143450071040000 + d *
    (-515836169590519511062264155756288492631226461978624 + d *
    (161001270630692141890273685079586482539940254056448))))))))))) + d ^ 12 *
    (-43171924844048065803011323053958896620272007774208 + d *
    (8036775574818731674272822849252967164917029535744 + d *
    (549352325650369744747937855674062165798581698560 + d *
    (-1662294860667261307533578590738585760497888395264 + d *
    (1182982701649093658549891790836982812885623504896 + d *
    (-645732837416843223897832180318583652624259874816 + d *
    (310307677137872679212524271613526134655036424192 + d *
    (-137482696660287401285238938748670671280654254080 + d *
    (57347291738032552889808551230785960162659139584 + d *
    (-22771232030303762842443331438307575474500665344 + d *
    (8662037080244367115485884706305782632351531008 + d *
    (-3168407191337456586811201842218192042125426688))))))))))) + d ^ 12 *
    (1116796374948383992254666271599074701862502400 + d *
    (-379703494179873842003305001421949060633853952 + d *
    (124536251230777820412537116225644310561816576 + d *
    (-39379738973943240297842164870070261072527360 + d *
    (11991634840574567755880270413658535659831296 + d *
    (-3510542967052102389080303979330357523120128 + d *
    (985641988639309855410751482918373827805184 + d *
    (-264523743770321586572506409636300648349696 + d *
    (67552670036811114578375878745619853475840 + d * (-16317012059773169487268483533352408186880
    + d * (3698292112012071462382015086213466685440 + d *
    (-778082133956407514702939209708796379136))))))))))) + d ^ 12 *
    (149631469253388269701469283211380785152 + d * (-25696456159974333871409117609781362688 + d
    * (3791488231966097664071432132435116032 + d * (-445438059688228222225126761146875904 + d *
    (33358529393001047135330648599822336 + d * (527769710830659409197621537931264 + d *
    (-611541155901030288827932386525184 + d * (93412772058511937696850285428736 + d *
    (-6181582071688117524191970590720 + d * (103506639143273107424731463680 + d *
    (-110236282135476267119149580288 + d * (49590460453166709322436050944))))))))))) + d ^ 12 *
    (-9275840515341559864167497728 + d * (759906148601009055027953664 + d *
    (32761964052793870442299392 + d * (-14941096295023443213287424 + d *
    (1372305055867708529967104 + d * (-4819390215915754487808 + d * (-6897502788291378544640 + d
    * (137316534183764951040 + d * (11575836373710536704 + d * (5028772356584636416 + d *
    (-297245524285718528 + d * (-55148942950137856))))))))))) + d ^ 12 * (1617074898075648 + d *
    (345248030785536 + d * (16128765329408 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt29 (d : ℚ) : ℚ :=
  1091556256463483114245240271583821329429988338033283 + d *
    (-50648550551807985826959232614303446355333364841903065 + d *
    (22773908602748085573393285049862213402229519446384961 + d *
    (64401860136191860342282631690327472517721849016873341 + d *
    (-98528140945991325741659565180541859358330284678179692 + d *
    (128728197916254604345756156567822786532424268304884173 + d *
    (-62870480589813607239365346172068441998987123743696687 + d *
    (-97191653845328567917381599945892506104171463934246486 + d *
    (214464444203594388194741165521499961983123873177118888 + d *
    (-230387954069177670250578358446993355886489129219089424 + d *
    (149206955614978129216837577986542037178579131652139068 + d *
    (8241145803557558655930440601335918249637447766205471))))))))))) + d ^ 12 *
    (-163598039971736964556374513171543062295305834100932616 + d *
    (236028257486408419708723474381894702852174111494214202 + d *
    (-211899409482693581470915676064492779903297627172609627 + d *
    (117594363520792067078177236808116403776952511464750666 + d *
    (5876726182791961376298018256411724728444615379146712 + d *
    (-109831645217815941518301013641982332964458040546977002 + d *
    (162241964216692176773196790786745575170580802598917357 + d *
    (-160097698070664474652699501329639913103493261756826167 + d *
    (118177572357659130654212365894255281578310476116582845 + d *
    (-58166341123367635161037651974238129563711357452875221 + d *
    (1690852109810928712498567126248570339309157603975475 + d *
    (37248838514827026110181579942921419429466072130145156))))))))))) + d ^ 12 *
    (-54857184765031322687729556102000750728663505256447594 + d *
    (54459001611390688782772442012623667743112163584507538 + d *
    (-42735693262687960779220533309030992612486740344531899 + d *
    (26815974089348129210105616747333210014773797494145283 + d *
    (-12055312263064600934067849309614328813759488920565799 + d *
    (1214616595921073426994285187753565066550438161957221 + d *
    (5083323974926637649510673367229943174471408714061890 + d *
    (-7530469426321923084656279138963228566072555633630125 + d *
    (7389086874397748020893686735611353875972445643894281 + d *
    (-5916337729549970015483953268885729136695233656189447 + d *
    (4053054937934266125226815019504478382477637473955252 + d *
    (-2361498675970227782438322040994653500155070789227432))))))))))) + d ^ 12 *
    (1089252174422700919888200668277868940111183113780022 + d *
    (-270902645914863705484944970971200040768462493126704 + d *
    (-170867701375914687300018636229606077902831888362867 + d *
    (349142729658617512493548608187121337852596484087950 + d *
    (-369746908349302941810039401306668650179911880554115 + d *
    (313320000602481273040201089055968512386506282422017 + d *
    (-232158666158703837148867759831528350786542737644793 + d *
    (154823010652305658404073338378495519914105664400023 + d *
    (-93413618393988309755520009607698165108907574553174 + d *
    (50272510594855816248854075944182667704555450829287 + d *
    (-22941868721317690879640329008773199025485446672099 + d *
    (7350857058972970299563676056008667303352505577227))))))))))) + d ^ 12 *
    (455332087694999741586266950436787640904864616342 + d *
    (-3604650967043757767634404400385745840230079737661 + d *
    (4269189369771484156116110758933927164778648402759 + d *
    (-3803246396757678874963428383624339525137444600718 + d *
    (2965001635494393647058415965569408641225182527929 + d *
    (-2126887790730804968168328991785295950431197856965 + d *
    (1436692331313367260468095923936555054489041363244 + d *
    (-925509638839031157680933349456714824099459922344 + d *
    (572952436848885329694330343647357739248529523490 + d *
    (-342544483408559063988884959844084537782164436451 + d *
    (198433267910383807001364610817387444209794887194 + d *
    (-111632710457188505012565329904970555178635214291))))))))))) + d ^ 12 *
    (61080977463799995722298604055900569980923363241 + d *
    (-32537566097959976809629780887118670004084337642 + d *
    (16884430125548512160284977147290687226030310685 + d *
    (-8537480233384101197616865320196526074502768719 + d *
    (4206394595359127934734324618617353611731249745 + d *
    (-2018861439445622710710697151008074141145935404 + d *
    (943373928996386607819756987136700530527364821 + d *
    (-428821204376592153466154611354655051377486931 + d *
    (189389175909875835999443319113418470732685060 + d *
    (-81130258655053933737858070594229566840330259 + d *
    (33630423197817819010376825105556561354147469 + d *
    (-13444102211978219920761187964157410441237283))))))))))) + d ^ 12 *
    (5156757971434430204881799016940308199829886 + d *
    (-1882744547745001417295025698579250068457364 + d *
    (645485548680284344830332465997360304095527 + d *
    (-202512980556345771770511446381587812271525 + d *
    (54772631223813538451667614035702910936940 + d * (-10412098154350718336061367031712214690439
    + d * (-566714517808462539447611412817909430188 + d *
    (2059591860667054268843686168055227637770 + d * (-1490076313971684051152129937923891812009 +
    d * (821080246255479745183823682780650573815 + d * (-397569470271388134844906251988970387515
    + d * (177360833313820117528879221867269639272))))))))))) + d ^ 12 *
    (-74472398591698760558262677801074302092 + d * (29763000497642116805701752709445976707 + d *
    (-11392733183388671400539764490419422358 + d * (4191978723971882649662608437825110151 + d *
    (-1485731529724017917339144781413297340 + d * (507734789156583016176229271522485017 + d *
    (-167332439436780746658200776530089448 + d * (53142240200395924918445161128519101 + d *
    (-16235481413013090473541299857031164 + d * (4759526762625177711232684610384886 + d *
    (-1334876630426624367574690666138867 + d * (356946922380776658147193645742758))))))))))) + d
    ^ 12 * (-90574731346011532676647897919271 + d * (21643265565194819298351943604674 + d *
    (-4809146922402486542607258390002 + d * (974728213245522275623516731581 + d *
    (-175316424499625251637320208492 + d * (26894445511593801994745762236 + d *
    (-3298647796463002631773185690 + d * (281102513902272764495600888 + d *
    (-8725083982986947518329759 + d * (-1367551723924374663714988 + d *
    (144620828472535091958116 + d * (10368108304806451421885))))))))))) + d ^ 12 *
    (-31947633755561204176 + d * (-1400940745101647409144 + d * (394022237685723809472 + d *
    (-52872539728556214053 + d * (3034887522036419007 + d * (134002279262124303 + d *
    (-31007762898431679 + d * (1082859788888626 + d * (13464866459235 + d * (11707472488941 + d
    * (-555463826007 + d * (-172464014009))))))))))) + d ^ 12 * (5099672929 + d * (1234981012 +
    d * (58452256 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_29 (d : ℚ) :
    orderSevenSelectionPolynomial d 29 = selectionExpandedAt29 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 29 =
      selectionNumeratorAt29 d := by
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
      selectionNumeratorAt29
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 29 =
      selectionDenominatorAt29 d := by
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
      selectionDenominatorAt29
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt29 selectionDenominatorAt29 selectionExpandedAt29
  ring

private theorem selection_cofactor_eval_at_29 (d : ℚ) :
    (selectionCofactor d).eval 29 = selectionCofactorAt29 d := by
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
    selectionCofactorAt29
  simp
  ring

private theorem selection_factor_at_29 (d : ℚ) :
    selectionExpandedAt29 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 29 *
        selectionCofactorAt29 d := by
  unfold selectionExpandedAt29 orderSevenDualKernelPolynomial selectionCofactorAt29
  ring

theorem selectionEvalAt29 (d : ℚ) :
    Internal.SelectionEvalCertificate d 29 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_29, selection_cofactor_eval_at_29,
    selection_factor_at_29]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 29 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt29 d
#print axioms solution
