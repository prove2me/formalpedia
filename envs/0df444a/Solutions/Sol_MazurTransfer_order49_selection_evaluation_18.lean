-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_18
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:19:25.217104+00:00
-- url     : https://prove2.me/submissions/1a417ba6-1acf-4b83-a611-fb8a49d2a820

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval3.At18. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 18

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt18 (d : ℚ) : ℚ :=
  -2112129723838464000 + d * (-426712627802419200 + d * (1032425283833095680 + d *
    (-2263715761882337344 + d * (3254168224096811136 + d * (-1864690000864258560 + d *
    (-832311732815045952 + d * (2942466726030403200 + d * (-4059344361061476480 + d *
    (4048126030294163008 + d * (-2772715141651735488 + d * (1012539970333699776))))))))))) + d ^
    12 * (527976107577864256 + d * (-1642893703157515584 + d * (2258975862900168576 + d *
    (-2358035011494802752 + d * (2092829236549474944 + d * (-1663842953693850432 + d *
    (1204916477154496384 + d * (-799375901051405184 + d * (491695023706249152 + d *
    (-283026214262778816 + d * (151357912271911680 + d * (-74321959836258816))))))))))) + d ^ 12
    * (33696406360555200 + d * (-14351513531465664 + d * (5697460987163904 + d *
    (-2017755240307904 + d * (621734646750336 + d * (-181636199613504 + d * (59817024272448 + d
    * (-20969424572160 + d * (6025119932544 + d * (-1233547592448 + d * (236792823936 + d *
    (-81461435136))))))))))) + d ^ 12 * (28304167296 + d * (-5371009728 + d * (390814272 + d *
    (-63775168 + d * (48979008 + d * (-10594752 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt18 (d : ℚ) : ℚ :=
  -2503110167022698496 + d * (-545894680280426496 + d * (1560465832301070336 + d *
    (-3626805447502986240 + d * (5660586733347926016 + d * (-4739260439584342016 + d *
    (1670254709540825088 + d * (1081128913066892800 + d * (-3147405389057367552 + d *
    (4543247713610420608 + d * (-4488058391500849792 + d * (3359109300636209600))))))))))) + d ^
    12 * (-1946700387785184768 + d * (593382273789682304 + d * (456083962422469376 + d *
    (-975292492941398080 + d * (1038622835164117952 + d * (-876005059894777280 + d *
    (647168359676542144 + d * (-434447920028282304 + d * (276204898956848384 + d *
    (-171884511335886144 + d * (104121262686075008 + d * (-60415823597923456))))))))))) + d ^ 12
    * (33797375927903680 + d * (-18440345668911936 + d * (9730088260960384 + d *
    (-4890871445561984 + d * (2334348835158592 + d * (-1056860622220864 + d * (448684364462400 +
    d * (-176510961993408 + d * (64433097886272 + d * (-21869514204544 + d * (6716079821696 + d
    * (-1744780641280))))))))))) + d ^ 12 * (347381920256 + d * (-44966855168 + d * (1990437888
    + d * (385820672 + d * (-52530176 + d * (-1342464 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt18 (d : ℚ) : ℚ :=
  1941338756048742233811434318780478702204416632276647936 + d *
    (-88957207990404767832476005697566618986045459862244032512 + d *
    (11324578872971996827293761588959639551935264513989804032 + d *
    (248149212449813249023253343637273297788356882180301914112 + d *
    (-488079466051603837212786177779827099792267835703407149056 + d *
    (575134633202922374006399323841587762947084799591053262848 + d *
    (117286822311554316201583616819549760644138990338616328192 + d *
    (-1730526658883184901565644692180401880982162607640057741312 + d *
    (3333712543335389721048686281772359372100271270090170695680 + d *
    (-3544306566438272043673277769111323100349780287770987331584 + d *
    (1072313715564935339560714459936732010776242785996626460672 + d *
    (4309043718786380266293326239982693946957920178116822040576))))))))))) + d ^ 12 *
    (-10568113014235397914501274585306206865224820790509708509184 + d *
    (13958548206761312765570033939772430534514982586681360384000 + d *
    (-10955372041754030751351282728139618363958760684195698180096 + d *
    (166987517536788807946679531864418458258475429987667410944 + d *
    (16156570663748680899859092577724504725480548405273463357440 + d *
    (-32129901241125492518871940250753459759751683388065975369728 + d *
    (40466915563703119494142775858756896708278941727694943420416 + d *
    (-35677066921670967590067000487680946004935001931025649238016 + d *
    (16652485217516296469803433601424906213412153018803198361600 + d *
    (12304912151192733839796912676577828711573728792305558355968 + d *
    (-42680325505260592111483050296841692213286612747253204910080 + d *
    (64819617216232303539598472238481240394565505070363512930304))))))))))) + d ^ 12 *
    (-71419703960800832063949946458975841645599706496201404448768 + d *
    (60015520470856795738193209543981842318734652334694325813248 + d *
    (-33658390100807942670904163449295131113627853891078813646848 + d *
    (-365351166911092886803686005979143845447137306248880324608 + d *
    (33143115797609726624055367897466097187551808406399609733120 + d *
    (-56948263214034747448062214818974010872818564645794866266112 + d *
    (67274489427572749408546161458430663596434245930958484144128 + d *
    (-63584174565460658353132894457243514643836001249703744765952 + d *
    (48767021489595919473532267071261458331006714191396695703552 + d *
    (-27734981293577830845889325893149204601240149662229974220800 + d *
    (5777862030292070151750913764456836280952395340969255895040 + d *
    (12785039031969207691344581869833907503203472300224068190208))))))))))) + d ^ 12 *
    (-25362555208045171516601558855159834435749430320179559792640 + d *
    (31216131958614584757651061804660349392248143483051164565504 + d *
    (-31102429813791726683433352111377095953399321933379102834688 + d *
    (26675824139162600664292221885936179530073877238248871821312 + d *
    (-19877363285585614215861143703520693311649044568394094346240 + d *
    (12461062389910465255447142606829505787234380796270093008896 + d *
    (-5720446985573888872280396562215528968683912900207282487296 + d *
    (405944197179947597539485401329915498580491542812340256768 + d *
    (3219185983752248549284993772749011144343077468363965595648 + d *
    (-5248859873088006020623321695915097340951226963500427902976 + d *
    (5985641043920199791252797696625446092013004853805774536704 + d *
    (-5810964188218061692680213833017683509670208775096455135232))))))))))) + d ^ 12 *
    (5092247484938689693139552838470323268368944660300689833984 + d *
    (-4129785111068201537685793290851791132259447006138241646592 + d *
    (3136968330594589652757302925387740492611375189410067775488 + d *
    (-2243499784425179356000778342438219896402718291435510824960 + d *
    (1511208551676517951519251329351103395602907944081683644416 + d *
    (-954157320561890929900810305532554766715783123074442854400 + d *
    (557591713129669307898532778609868201946158800647005929472 + d *
    (-292957653769298481147147325927404318300069421387639685120 + d *
    (128214338785497378566489747265232042050815533026625454080 + d *
    (-33893002888856435416301649849592909236903219746550054912 + d *
    (-14090975756952111989610415395701979009190940826025590784 + d *
    (33771905781355611385800158948004956158844943786957340672))))))))))) + d ^ 12 *
    (-37676175129778286011368862949804904135732474326628171776 + d *
    (33893011151166533125899085944826029225813662707074203648 + d *
    (-27244973989343235629258821903014895859689093186002616320 + d *
    (20329571058795524973035643107689124007853157200941547520 + d *
    (-14340652201403679005630405456098602733260020133352701952 + d *
    (9660137499074201607396437977915439204013346559565234176 + d *
    (-6251569029630845427153597345000399764045734863331917824 + d *
    (3901418642314041509201694243671764542950944675436429312 + d *
    (-2353511676296623406136005151427664565583772763731263488 + d *
    (1374346008508068898332124239462688924745972022598434816 + d *
    (-777474155392323011580408825017236939737251685276057600 + d *
    (426148361150832122413971164708410886838122295327195136))))))))))) + d ^ 12 *
    (-226235743805737557091675966608287461127271850366205952 + d *
    (116218682861995421919908012444530716222513092697784320 + d *
    (-57674847113042534765122651890092395811994258421317632 + d *
    (27577468479466718607051055260264925078426067977109504 + d *
    (-12653451531115540669612898055928287352330576126279680 + d *
    (5535212652327834941190769795892206220093683231096832 + d *
    (-2283515560237556882140238794461216631747139641802752 + d *
    (870808188996541179885237348873938236422998198059008 + d *
    (-294063896029695612462351157675147470162150541492224 + d *
    (77764011500318192699591380828506356993063026688000 + d *
    (-6925504595069900624845162059440994576871412465664 + d *
    (-10372700030062751220166293701719216901628027207680))))))))))) + d ^ 12 *
    (10753094904731137198608001824529003629045391556608 + d *
    (-7412764093840600731241156296907334437013396652032 + d *
    (4348450184732919540181693248066963292072540110848 + d *
    (-2320560832580461931224513881571340451118746173440 + d *
    (1158324110121603007263653761941521553111760240640 + d *
    (-548489757006175795892005914239153114691663560704 + d *
    (248352493621554035052794717085748665243927576576 + d *
    (-108044407506936802410043041778258673238056370176 + d *
    (45293208778627715372917386528558848690336825344 + d *
    (-18327705587874321355504152440049387005244866560 + d *
    (7164996479839043270366703352643988054340534272 + d *
    (-2706907331112643121096673928401008773527240704))))))))))) + d ^ 12 *
    (988034987635406270561436916146390048946782208 + d *
    (-348181752154286300922883404668304804725653504 + d *
    (118326410018282970754471812177168494375731200 + d *
    (-38718718250346816298378016686268200539127808 + d *
    (12174276086517999842566182040014636595806208 + d *
    (-3668825153683940996911708887249100173475840 + d *
    (1056210436556558293739580198330017893580800 + d *
    (-289274115849291538802536296177883546910720 + d *
    (74974797694259389323984208517157327470592 + d * (-18266370061354761614153865178500172349440
    + d * (4147278671803633312191626191823055618048 + d *
    (-867535851347751954457071114064653975552))))))))))) + d ^ 12 *
    (164589884267702974846421296439832346624 + d * (-27675988494507182874379480741296996352 + d
    * (3972555365906298074171353372051374080 + d * (-452090328445296872362996932794908672 + d *
    (32910264705376825977320324832690176 + d * (378359716324433701210802290163712 + d *
    (-519654082383520672859984022994944 + d * (74669921695278935835692941967360 + d *
    (-4568781828010685244174840365056 + d * (216921043975101542022752763904 + d *
    (-160666677942985829724429746176 + d * (55432843146433402156744704000))))))))))) + d ^ 12 *
    (-9394181790497022107953397760 + d * (718062428018691620247437312 + d *
    (36116003235462839309697024 + d * (-14821927529945564362833920 + d *
    (1366592304124555601641472 + d * (-7938772908145897373696 + d * (-6870137084772200218624 + d
    * (174782152539093336064 + d * (11788239244284919808 + d * (4816979194269663232 + d *
    (-310641093125865472 + d * (-55655883522703360))))))))))) + d ^ 12 * (1602570251403264 + d *
    (345090471755776 + d * (16128707657728 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt18 (d : ℚ) : ℚ :=
  162807387700903025667573876441866394572685312 + d *
    (-7432695899618502316856314784124046190290403328 + d *
    (-362508836357465989427926917956513616991617024 + d *
    (23246171599828943499595420101904739725932920832 + d *
    (-38606418008777968363941200555415935032010612736 + d *
    (33996862325156603333148026262454552667500022784 + d *
    (34732225898525522292505419363828879213484508160 + d *
    (-160482405429930055999606494364599484284231441408 + d *
    (246656083192122485278157368331683450535887035432 + d *
    (-187591350287087992500843795750278317026622804913 + d *
    (-70387692966948298526290320822287980984687799074 + d *
    (471951913175570028098767126293419403460905180443))))))))))) + d ^ 12 *
    (-808123161341247613574036800377719421297045816575 + d *
    (815356439817185030090165711872741624698358100716 + d *
    (-346740066283359417084648986762895329777014490745 + d *
    (-531490109479758778760756645212974681599903410818 + d *
    (1524959437063961715217318978730838162494069815942 + d *
    (-2202186809696295513239627578018821762614814266402 + d *
    (2191739765796393683730736212748694588341012938838 + d *
    (-1362857193468648028453046228788395835963690185264 + d *
    (-107269297893607199802920513301449038213397096938 + d *
    (1785739046084039085485062989877106534952376155049 + d *
    (-3139179103339587163215470426941621134417692170330 + d *
    (3734509853411275071141504448661729364621867047528))))))))))) + d ^ 12 *
    (-3389049631358053018956117327117138468094000453127 + d *
    (2214040656592045571600714141530180293239180069180 + d *
    (-554704832980288785375287899623186463355415294603 + d *
    (-1140344825796376190641870672181794878518293056892 + d *
    (2466482288379637787899400934863965664308173526317 + d *
    (-3171065828633469671825814338170409060971255657425 + d *
    (3194161503620092957265250896995204267685590624441 + d *
    (-2645912905475664903275511206834479184006721478084 + d *
    (1742120855758231664479820463185243782747276024879 + d *
    (-726979604852089345657605630970551276786895770601 + d *
    (-190950287911510750637772315380325271400753615282 + d *
    (875650757530708614792694176449677414508567313141))))))))))) + d ^ 12 *
    (-1272357091699200955304534460819413209441688891834 + d *
    (1394853225117342915069704491684947310886723684421 + d *
    (-1301471122865092754646171897668879062455120041670 + d *
    (1069498042509728233779602539664298813369275531455 + d *
    (-774500286691436764823444842941224862379057002446 + d *
    (477294290419014484951308221832956405985140164707 + d *
    (-218478612834599668648406125228536351368140377881 + d *
    (18798403519953976905488177167129338859880641377 + d *
    (116996319306627881850705368943016193512235845575 + d *
    (-194933756731635758025240289398344229926340182913 + d *
    (226769291268063659902066920615082425210700512137 + d *
    (-225964317807496292707585745308395865683645338851))))))))))) + d ^ 12 *
    (205005339354185982427981966989519519611568506887 + d *
    (-173984295246886637264784759424651592817390716879 + d *
    (140153829803628100289948189565346695712063959044 + d *
    (-108114082028359019289556633179763870499300358135 + d *
    (80322975582192939364525264981359700301941177649 + d *
    (-57700944543178875439774537355760581400830243614 + d *
    (40188953207135566093159897360658921849410044893 + d *
    (-27192906961788425951918692397294952967373144582 + d *
    (17898674403979775281771208858102197465816053825 + d *
    (-11471019359190584244318740905000512570928545936 + d *
    (7162217210661716753414697602223767316861165061 + d *
    (-4357933111314231436073499370458206385598727991))))))))))) + d ^ 12 *
    (2584136644185691619164978570533552351795482408 + d *
    (-1493019691591219080131845743487870200579381939 + d *
    (840123723727470986267099183178159834706572744 + d *
    (-460099334633360094951185087921696313145587909 + d *
    (244999068968971904240038298699256990498560868 + d *
    (-126675130218326112057820315387971719921758553 + d *
    (63477339571570194599203681096448232353485531 + d *
    (-30747524937268139910053621860359618036519299 + d *
    (14342815418995586466855408511184336489036417 + d *
    (-6406913508515481361036131313701736235995790 + d *
    (2716243697911570860771875645116206999845777 + d *
    (-1076114760333499990875334056187732471137452))))))))))) + d ^ 12 *
    (386384618537233506458694970737146008444208 + d *
    (-116610073861594787169519885726362990085959 + d *
    (21870003599462772314425857988286341810949 + d * (5379085212963653219794892660513903757004 +
    d * (-9519337428091055675290072560157959764466 + d *
    (7392560465952368498016418695849722290273 + d * (-4599291690385303418527720720457105924772 +
    d * (2550463722994719660858484999734752281864 + d *
    (-1310499430307914381109861795290536716606 + d * (635501674095098823259912710904519405727 +
    d * (-293755206294607372848743979713656576521 + d *
    (130188309630460027959493098262087211285))))))))))) + d ^ 12 *
    (-55512635341748692802008002399376647794 + d * (22820712698792171410365707882505311806 + d *
    (-9054019523393241826019748924095912068 + d * (3467973712143096227954629083012316986 + d *
    (-1282123018513466878606596545406707786 + d * (457161010177835569158179204533686595 + d *
    (-157008371411498699026099825315151950 + d * (51840777249247959593156752290088152 + d *
    (-16415135434291050369181311048451849 + d * (4969381918815625744545627133157866 + d *
    (-1432719469010315559756139338258089 + d * (391390725628082578015995657725063))))))))))) + d
    ^ 12 * (-100605362414470412877334180457980 + d * (24098216101655219833791410996613 + d *
    (-5308042666921676288704312722748 + d * (1056062727010168131635606260802 + d *
    (-185208722943685066835027485696 + d * (27643340012048281393120085831 + d *
    (-3315473749671063801134219634 + d * (283893762439682316361508600 + d *
    (-11522058590211599161895359 + d * (-581750205993662570321207 + d * (32037970906865021292645
    + d * (16773936316281302397363))))))))))) + d ^ 12 * (632463563074793976547 + d *
    (-1556838120599624747798 + d * (403004915056298293686 + d * (-52518935386018225225 + d *
    (3011612712033059268 + d * (127934581445725986 + d * (-31078512158526302 + d *
    (1181152258521500 + d * (14525477972768 + d * (11044636045155 + d * (-599689015323 + d *
    (-174127082031))))))))))) + d ^ 12 * (5050756171 + d * (1234422212 + d * (58451959 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_18 (d : ℚ) :
    orderSevenSelectionPolynomial d 18 = selectionExpandedAt18 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 18 =
      selectionNumeratorAt18 d := by
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
      selectionNumeratorAt18
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 18 =
      selectionDenominatorAt18 d := by
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
      selectionDenominatorAt18
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt18 selectionDenominatorAt18 selectionExpandedAt18
  ring

private theorem selection_cofactor_eval_at_18 (d : ℚ) :
    (selectionCofactor d).eval 18 = selectionCofactorAt18 d := by
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
    selectionCofactorAt18
  simp
  ring

private theorem selection_factor_at_18 (d : ℚ) :
    selectionExpandedAt18 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 18 *
        selectionCofactorAt18 d := by
  unfold selectionExpandedAt18 orderSevenDualKernelPolynomial selectionCofactorAt18
  ring

theorem selectionEvalAt18 (d : ℚ) :
    Internal.SelectionEvalCertificate d 18 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_18, selection_cofactor_eval_at_18,
    selection_factor_at_18]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 18 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt18 d
#print axioms solution
