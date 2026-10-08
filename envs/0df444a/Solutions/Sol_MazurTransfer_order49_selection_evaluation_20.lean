-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_20
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:31:39.149978+00:00
-- url     : https://prove2.me/submissions/532b3513-7abb-4be9-ba94-13736109751a

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval4.At20. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 20

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt20 (d : ℚ) : ℚ :=
  -7437713408000000000 + d * (-1291281543168000000 + d * (2824243103322624000 + d *
    (-6202745031059553344 + d * (9222967415974571904 + d * (-5616268424480764416 + d *
    (-1167121558617915840 + d * (6010284494363493504 + d * (-8440911852841080576 + d *
    (8562815724975080512 + d * (-6041418742167799488 + d * (2656898148807787968))))))))))) + d ^
    12 * (142018892972836544 + d * (-2104336764702982464 + d * (3192959291018932224 + d *
    (-3388984118132006976 + d * (2983298681972155776 + d * (-2336925207099660096 + d *
    (1662974336001214336 + d * (-1080657021160043904 + d * (650483958395373888 + d *
    (-367249046043715008 + d * (192845525020849920 + d * (-92788515980694528))))))))))) + d ^ 12
    * (41191122966861120 + d * (-17267727438383040 + d * (6792797885198976 + d *
    (-2381616378965696 + d * (719796324651264 + d * (-205002868535616 + d * (66792705911232 + d
    * (-23445085952256 + d * (6677230336128 + d * (-1327353989376 + d * (245488330368 + d *
    (-85581851136))))))))))) + d ^ 12 * (29964797184 + d * (-5586645696 + d * (377879616 + d *
    (-59475904 + d * (49264704 + d * (-10590144 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt20 (d : ℚ) : ℚ :=
  -8814624768000000000 + d * (-1644339601612800000 + d * (4287972855947264000 + d *
    (-9921289990382407680 + d * (15672719329377245184 + d * (-13090958890030066688 + d *
    (5178379680037040128 + d * (1236365645479100416 + d * (-5745045715670362624 + d *
    (8916524879016047872 + d * (-8931985244886975616 + d * (6730372788779994432))))))))))) + d ^
    12 * (-4089854039495560320 + d * (1626874363388938624 + d * (287165490037985024 + d *
    (-1241472221448216768 + d * (1391635090055147968 + d * (-1172485664790046528 + d *
    (855491204272002368 + d * (-562253735042240064 + d * (348374141539066368 + d *
    (-212008224493860032 + d * (125748021242482304 + d * (-71074874702302848))))))))))) + d ^ 12
    * (38637274595789760 + d * (-20589987297683392 + d * (10658994217359488 + d *
    (-5252230769641088 + d * (2456288950225600 + d * (-1093743095652416 + d * (458326375986624 +
    d * (-177895694755904 + d * (64040344766016 + d * (-21548263006592 + d * (6621194960768 + d
    * (-1731597035520))))))))))) + d ^ 12 * (347205266944 + d * (-45106612736 + d * (1987310592
    + d * (388601856 + d * (-52249600 + d * (-1340416 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt20 (d : ℚ) : ℚ :=
  84818461736166293318074892288000000000000000000000000000 + d *
    (-3904156003915978137423807455952896000000000000000000000000 + d *
    (1002432492932116838796971415843907829760000000000000000000 + d *
    (8711852843775330012886873360038756091953152000000000000000 + d *
    (-17055240760600960294632170941613281665697710080000000000000 + d *
    (22070554880272930627200372469776774158667795660800000000000 + d *
    (-3464613443377398572760616686829942667468405420851200000000 + d *
    (-43165574548442431011342347905263500694707016370120294400000 + d *
    (90532874485940633790383987946262826883793522904342200320000 + d *
    (-104526394481546558186537173850645388478433558041305441632256 + d *
    (55651766607647331014129164940947403563559074717396839956480 + d *
    (62451472003516165844944359708975663056469456843714610069504))))))))))) + d ^ 12 *
    (-205642176463278267103785724946293433551970303818608749838336 + d *
    (296497810676559385474168343146632361755560054471318597533696 + d *
    (-268432029751997509302259294511717639541802666395690469949440 + d *
    (96805842796704094897002211748901295406456889850292556005376 + d *
    (179582274651668611259633155997254718612575063070139123761152 + d *
    (-462603035007509889069286996774578616605930456030004908130304 + d *
    (637046445148207079665464597263787999669444855176013681786880 + d *
    (-621428201575225056044422426945220916780526996669266536431616 + d *
    (400638233045577980888331768150895021520445400703553975091200 + d *
    (-33947933152362722468363035109710775853206428100680398143488 + d *
    (-366633304519056628324558556890176266256599370512770781413376 + d *
    (680113751386048692098186103409338223018866129342743634771968))))))))))) + d ^ 12 *
    (-819441894818742424556387765719102065102508266159158082666496 + d *
    (756687996791098040994957509629600245934804019039883773083648 + d *
    (-525543413997141938824325917955820131529381403546080663306240 + d *
    (202929426096015943823851948963224744649706624560996738924544 + d *
    (121026996889988449710254818695010939964530818383925055848448 + d *
    (-371378438159747491415745203803262671212686324510908311404544 + d *
    (505971708810095417753612321051779473022701619696496139567104 + d *
    (-519604818644966488270431239657241088375214274122893043433472 + d *
    (436655190701900498799291399507173142039658133257746924437504 + d *
    (-297298885697997124459154387609251474167285050672088975671296 + d *
    (143331636909764635680460623879761062320090588595365636734976 + d *
    (-7808836144686660650917096905662504766919251971194439598080))))))))))) + d ^ 12 *
    (-89902207398817884428851550655832433550654492740923447050240 + d *
    (144098779042442305864560737352806708531386891639444888879104 + d *
    (-159428181403837346506625247214772218437433832854439615528960 + d *
    (146320882278251804050642442283245361996225688510118763167744 + d *
    (-116781773164605450518449891321781212053755923167269990957056 + d *
    (81410257663784985396655434498953930609928755055198967693312 + d *
    (-47866532861407803660601669925080323821381391197289387130880 + d *
    (20559576030325083097500582970886915528300798401817870860288 + d *
    (-1124353408637493612631362533032677230734878565938876383232 + d *
    (-10747455364383902071253081170942203102747170861520034201600 + d *
    (16448225346203798299141794886911243780088947241816364417024 + d *
    (-17755252305095550794441926740360348643136505815967138316288))))))))))) + d ^ 12 *
    (16362844029080114788929318769901903181681181454627225206784 + d *
    (-13635485339834840451276506605385333814514522222940931751936 + d *
    (10530303330764256964219027781493339097313162224447071453184 + d *
    (-7626536807128216020405937046353551179102539116998452051968 + d *
    (5207203073346658247663984271118961590667841783935531745280 + d *
    (-3353379047029716950331845341481036091858952276842839539712 + d *
    (2027805702790937868108635866494198244621001652447254675456 + d *
    (-1137853388138241360031370159547210803744271984242592579584 + d *
    (576721844404492117419219507411740126258005569372469592064 + d *
    (-246431870315186858182909519214846176856918832194455339008 + d *
    (67796468980356586285702042949302611462893166651506950144 + d *
    (17676860824928840635056757296210051927488157844485963776))))))))))) + d ^ 12 *
    (-50097776395314233679212237168547469739988157978965442560 + d *
    (55131156598220109147806046109285026036872792168976089088 + d *
    (-48057166551378545923430466494155115523217969006319239168 + d *
    (37231107548884134204971460886223135684172396287021023232 + d *
    (-26712330161912895492119996693081720378034292303749447680 + d *
    (18096442043127380536005072054418058065518452309509799936 + d *
    (-11698720711250564384357133364697006102117465122302066688 + d *
    (7262231750303503774857999718401841246536614686266753024 + d *
    (-4345896222220075639152887104787908259781367780017438720 + d *
    (2513191744923140355153208164998360903062811492987174912 + d *
    (-1406514803530212316839523254799222095193096736243712000 + d *
    (762353070646172292659394259473738382946405505688928256))))))))))) + d ^ 12 *
    (-400239465607839535914123922373005727244099596817268736 + d *
    (203444219678057625576224101280119172719948045880918016 + d *
    (-100016274860771987474136469396354754204155534802157568 + d *
    (47467505042726364630578677722939902604372800967016448 + d *
    (-21684644663400961601921815474751119296887885740376064 + d *
    (9491682849497260400317178348501908696282766006550528 + d *
    (-3951359588455768134302232048057314575797766844317696 + d *
    (1544636825460997921896337730445431077606195955236864 + d *
    (-553380047230312328718987720250312996166146994995200 + d *
    (171886881201594060451417829263942564282566501466112 + d *
    (-38589201029616054804958284904245260380639050072064 + d *
    (-843274430616101266547403588973031663709976526848))))))))))) + d ^ 12 *
    (8411794762365326135522639837357886630420833107968 + d *
    (-7107601191699002574842082453667348175751763197952 + d *
    (4476367137117347791902149640765511227152895049728 + d *
    (-2462700969339967376420738784476240581739233935360 + d *
    (1245139712625119672951356812666857194719631638528 + d *
    (-591791953902504833286209875812332542441329262592 + d *
    (267563378111943861007029532176400145743056207872 + d *
    (-115867302670803791351164143480194733261191118848 + d *
    (48256760356447057137532994786612369916613885952 + d *
    (-19377412643608915303792472460467310239422873600 + d *
    (7512517174848854986968240652143009048521867264 + d *
    (-2813865240427062291189373835966627103357009920))))))))))) + d ^ 12 *
    (1018262716760335948864706486743470375955333120 + d *
    (-355827406253916138156295216381121569489158144 + d *
    (119956141885452050478380512050051404648677376 + d *
    (-38957835689163460303675220688487177752936448 + d *
    (12165702156777207130527333179914821200773120 + d *
    (-3644098763730504521684344718285234613780480 + d *
    (1043740578159449942586322498940124245000192 + d *
    (-284706848701226533693692355076438637674496 + d *
    (73581491432474095938792093505587879084032 + d * (-17899196831812330983218447237621248163840
    + d * (4063216159090562372209792957633634762752 + d *
    (-851009105038331655612099924480605814784))))))))))) + d ^ 12 *
    (161880209280364772423307989628306325504 + d * (-27326908231884205245116905819005517824 + d
    * (3941862810000896572029944993564590080 + d * (-451056372572070311839377418896539648 + d *
    (32966470851328679518426808219336704 + d * (415276557714989301986044251996160 + d *
    (-537665681922780412208340092059648 + d * (78123170238262785323942277021696 + d *
    (-4850462184768788183303158759424 + d * (194657488154965678039848976384 + d *
    (-151483456027150705974286745600 + d * (54381055449393533025635008512))))))))))) + d ^ 12 *
    (-9372458479585323739486879744 + d * (725542994074848881564712960 + d *
    (35500756855554437404950528 + d * (-14842095548003058329321472 + d *
    (1367693943262355588907008 + d * (-7379409151603562250240 + d * (-6875838925344381599744 + d
    * (167938998954983424000 + d * (11748711454047207424 + d * (4855475483677818880 + d *
    (-308205557134131200 + d * (-55563712509509632))))))))))) + d ^ 12 * (1605207459889152 + d *
    (345119118852096 + d * (16128718143488 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt20 (d : ℚ) : ℚ :=
  5240549295597289472000000000000000000000000000 + d *
    (-240422705691186926977024000000000000000000000000 + d *
    (23789787426516981016103485440000000000000000000 + d *
    (614632121301657055358422969253888000000000000000 + d *
    (-1018584762150834783961131240806891520000000000000 + d *
    (1034903335248097766952763849749320755200000000000 + d *
    (401801042799012795773231628526343621427200000000 + d *
    (-3164543483381872749758608702637408159578393600000 + d *
    (5180709793210796190652826973200094044063179080000 + d *
    (-4515313188382650627514955960770873471899945841739 + d *
    (324615994059804822060022313845078590542391126290 + d *
    (6497499267401745680700989363119105373904039879581))))))))))) + d ^ 12 *
    (-12573898386955954933152425146778430816256514318433 + d *
    (13863991636446437312684189464415083716763097552714 + d *
    (-8395935846456635438843368243750332314256869154597 + d *
    (-2813274715912567664255581213645419366855963635614 + d *
    (15948561508646042815314597581872222916329862962142 + d *
    (-25686362722575446266280356249172235324736907741432 + d *
    (27713162331080922879192558281375432754398559236312 + d *
    (-20693375881400516261889386600260761601998463419132 + d *
    (6606393028545511233767988340238164521582487630128 + d *
    (10112681891380620395113471570629735897420787612881 + d *
    (-24266460407262258173214130483361245355528252150692 + d *
    (31855597508231188887141230446487092278034770137624))))))))))) + d ^ 12 *
    (-31320442140194244496806486011848892803460863538575 + d *
    (23666865048657410121790522289333967706452710029866 + d *
    (-11748759244466037536449090908597802102146182332835 + d *
    (-902302602366573350393607345314323932550356049742 + d *
    (11247359138198832210730969116728054102722667952891 + d *
    (-17480009226752787835093156724246552734005534087761 + d *
    (19199324261831864358765986035158928840610125840111 + d *
    (-17144751452035934802214990757870951623386565154760 + d *
    (12698108459487639745457390823716754482472331042431 + d *
    (-7359994968047889689569041450147549519870119840355 + d *
    (2363023557297730328677899634751829523097765142316 + d *
    (1516248593154445191542951885122733521967292733009))))))))))) + d ^ 12 *
    (-3971543233288313744438669546537736812948740747144 + d *
    (5067603109592984483617062648627730315751865237357 + d *
    (-5093278293428389162658953911676765015865317796872 + d *
    (4421396322564959436843913144935636719361973991705 + d *
    (-3405915141455274910674201910053176841985406803634 + d *
    (2323796556452613136585976053169705222059191481759 + d *
    (-1355501399600185140020588865828690940820276043697 + d *
    (592172722816980043801046910673419312628116661617 + d *
    (-56655699383737513201637934683937308929351205511 + d *
    (-271889597412978381263713620750389876361415050981 + d *
    (436100872522208319667466052714477259884528998845 + d *
    (-484184150613423317629640027390792323328486488409))))))))))) + d ^ 12 *
    (459879507777215465068089781617459280987580360799 + d *
    (-397688761682292335224954418081640101354204082605 + d *
    (321817760774649927692780818850927951764791242590 + d *
    (-247296295827291251971864436901393148530674664131 + d *
    (182054144042281117439383016606585407313354733007 + d *
    (-129134357529354963066117669193152405902470058608 + d *
    (88598144744913422428399530808655066443452053311 + d *
    (-58954800728285756565000964976891700471049914380 + d *
    (38119290468630102000958815539452178816020346793 + d *
    (-23981071171654942573180626031786808310156819830 + d *
    (14691532540179626442805130811070517178777275083 + d *
    (-8769322834737031520329771224809436977321489975))))))))))) + d ^ 12 *
    (5101122447032992488424944221508092504807964516 + d *
    (-2891723571064321305471861346781670183762487203 + d *
    (1597080607187485071339680641098188368846271060 + d *
    (-858931492915988973389896900092680147811713539 + d *
    (449487399301069954727552739498459256365002966 + d *
    (-228627544329482175010164100892847830473312925 + d *
    (112858220343706592033707890314497213804374321 + d *
    (-53953395007322242214464335731261674157728079 + d *
    (24905660176364083282327986190642917426328185 + d *
    (-11053421509849851902102975741673039406538954 + d *
    (4685447170939348419894370763725382761334377 + d *
    (-1876611439199345434966725260034917941044660))))))))))) + d ^ 12 *
    (696462863206704622703077179174261567891654 + d *
    (-229862432575648613078492335493445762702757 + d *
    (60154984051960653966149440469193841360553 + d * (-6154320223678771265477288847966554732722
    + d * (-6719492171256845631070654887186835206750 + d *
    (7067581890462062410404626227386833803729 + d * (-4790497761883439183025328013780909018260 +
    d * (2746291747492360940808363595300575249814 + d *
    (-1429033842550971939251773231851852649624 + d * (694749724741372881452551787434814738131 +
    d * (-320190418443340943071012800315293754607 + d *
    (141030365101881786255865324310024390941))))))))))) + d ^ 12 *
    (-59651889636227235972737914349771225732 + d * (24298244018475580640368273613131144886 + d *
    (-9546637511869357429354096193863925170 + d * (3620432579883462514673028239748594696 + d *
    (-1325345486226915897859958436386183682 + d * (468088586798630281907430767024132409 + d *
    (-159320971154198907700528933267442076 + d * (52168941019964651038546336960864316 + d *
    (-16395655429437952655520616828141273 + d * (4931121147526673498039580807798768 + d *
    (-1414074953212764081268650921189325 + d * (384796123072906719587745460699087))))))))))) + d
    ^ 12 * (-98703145737519665542652108991318 + d * (23640341785831958565437856384043 + d *
    (-5216908385288393257394161992902 + d * (1041564118910019601589955293462 + d *
    (-183498857546791643887910629586 + d * (27520106874911532574923319483 + d *
    (-3313017803360608698382773378 + d * (283231242014851450726255172 + d *
    (-10977421562014632792741513 + d * (-727414494299120017587001 + d * (52417853055570352948229
    + d * (15635886822614026644161))))))))))) + d ^ 12 * (512015791694563913243 + d *
    (-1528722564308659435206 + d * (401355686168633128494 + d * (-52580012528623677857 + d *
    (3016027545975092142 + d * (129017276505145698 + d * (-31067779982656356 + d *
    (1163187156100576 + d * (14329848677736 + d * (11165114446029 + d * (-591648152505 + d *
    (-173824706027))))))))))) + d ^ 12 * (5059650127 + d * (1234523812 + d * (58452013 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_20 (d : ℚ) :
    orderSevenSelectionPolynomial d 20 = selectionExpandedAt20 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 20 =
      selectionNumeratorAt20 d := by
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
      selectionNumeratorAt20
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 20 =
      selectionDenominatorAt20 d := by
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
      selectionDenominatorAt20
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt20 selectionDenominatorAt20 selectionExpandedAt20
  ring

private theorem selection_cofactor_eval_at_20 (d : ℚ) :
    (selectionCofactor d).eval 20 = selectionCofactorAt20 d := by
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
    selectionCofactorAt20
  simp
  ring

private theorem selection_factor_at_20 (d : ℚ) :
    selectionExpandedAt20 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 20 *
        selectionCofactorAt20 d := by
  unfold selectionExpandedAt20 orderSevenDualKernelPolynomial selectionCofactorAt20
  ring

theorem selectionEvalAt20 (d : ℚ) :
    Internal.SelectionEvalCertificate d 20 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_20, selection_cofactor_eval_at_20,
    selection_factor_at_20]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 20 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt20 d
#print axioms solution
