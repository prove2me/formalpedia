-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:46:06.833539+00:00
-- url     : https://prove2.me/submissions/f11410a4-ab0a-4a0a-a3ed-33bec7d79ab1

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval1.At6. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 6

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt6 (d : ℚ) : ℚ :=
  -4423866679296 + d * (-5125605765120 + d * (24583050091008 + d * (-47634728721472 + d *
    (13803553171584 + d * (195317861260800 + d * (-640515452495424 + d * (1115003037319296 + d *
    (-1010822790193536 + d * (-697584337609664 + d * (5167609488748608 + d *
    (-13101140636396352))))))))))) + d ^ 12 * (24267921475314496 + d * (-37360239285271872 + d *
    (50188715351357568 + d * (-60271649196539712 + d * (65627615430083712 + d *
    (-65344127495929152 + d * (59772207966770560 + d * (-50365075170696576 + d *
    (39147296087093952 + d * (-28048217816478144 + d * (18465251796374784 + d *
    (-11122625250548736))))))))))) + d ^ 12 * (6104742863956416 + d * (-3035541401394624 + d *
    (1354071245495808 + d * (-537234674186432 + d * (192427578048384 + d * (-66568653306432 + d
    * (24113589966144 + d * (-8775190025472 + d * (2766497165952 + d * (-696522945792 + d *
    (167162193024 + d * (-54762646272))))))))))) + d ^ 12 * (18592371840 + d * (-4071581376 + d
    * (468422208 + d * (-89570752 + d * (47264832 + d * (-10622400 + d * (326592 + d * (122496 +
    d * (5184 + d * (64))))))))))))

private def selectionDenominatorAt6 (d : ℚ) : ℚ :=
  -5240401920000 + d * (-6914804889600 + d * (38291965913088 + d * (-92487930067968 + d *
    (114387461013504 + d * (60837254428672 + d * (-608494642692096 + d * (1487995688693248 + d *
    (-2359329743291904 + d * (2454963890905216 + d * (-671381960851072 + d *
    (-3906377189493568))))))))))) + d ^ 12 * (11525878847830272 + d * (-21450531113259904 + d *
    (31881454676926208 + d * (-40502706666991936 + d * (45457093849758656 + d *
    (-46054619594584256 + d * (42889339447665088 + d * (-37389226765561536 + d *
    (31048091466227456 + d * (-24860601569165376 + d * (19267844139460736 + d *
    (-14403793250382976))))))))))) + d ^ 12 * (10311251540840896 + d * (-7016047275302976 + d *
    (4509955238110336 + d * (-2723786764565120 + d * (1535532485327680 + d * (-801899178690112 +
    d * (385236734423616 + d * (-169222845105600 + d * (67358212000320 + d * (-23851854183808 +
    d * (7275923356544 + d * (-1822531910656))))))))))) + d ^ 12 * (348660492800 + d *
    (-44125385216 + d * (2009201664 + d * (369133568 + d * (-54213632 + d * (-1354752 + d *
    (144384 + d * (83968 + d * (6144)))))))))))

private def selectionExpandedAt6 (d : ℚ) : ℚ :=
  17463297227675023564178515542813966336 + d * (-646613611942537434641830081497252495360 + d *
    (-3906879312080280041020699376401313169408 + d * (17589614025903308067076718271925548220416
    + d * (10771802020988894484988749141226523983872 + d *
    (-262149445006974953943287112523285253849088 + d *
    (847681108506753892300630704549087519178752 + d *
    (-525364268216949923022827546475314162958336 + d *
    (-5687780486158039438979117887636288919568384 + d *
    (25269961532513073261780969315832019892305920 + d *
    (-49912583743708379979407205454316913046061056 + d *
    (5274248321232083123944946860418394578485248))))))))))) + d ^ 12 *
    (308367632502066563445676678027537438700732416 + d *
    (-1147869488786450226226718117679993253720752128 + d *
    (2335464741931103521455003248179371440668147712 + d *
    (-2050933474410397282629911280252919396154736640 + d *
    (-4777366452078318877106304695099935261973544960 + d *
    (26497286263817420056999180907110341353327820800 + d *
    (-68682999956872396588380611976841985359460433920 + d *
    (116131688813544713164562198103736797376987529216 + d *
    (-101017049071514860361765751088749769675124506624 + d *
    (-130025874179187922637866384658932547560559345664 + d *
    (809877886611654238214614198762843901071146352640 + d *
    (-2134802136674278123499606516766069013393286103040))))))))))) + d ^ 12 *
    (3957062452827809431565933768897323046725648384000 + d *
    (-5256003627216950824808197781154697381784841355264 + d *
    (3506276979973997229696577231737886990728860794880 + d *
    (5687990626909820812557088169765591141996113690624 + d *
    (-28039757152607285907543627844558212976846080835584 + d *
    (68285540450009494492448044281469927058940486221824 + d *
    (-125485059333900931272475557772533061157067970052096 + d *
    (185891510901315948564215224791571473830670295891968 + d *
    (-214513106927698745452874372889529447090855712653312 + d *
    (147877004767959554733077270407926239236091191754752 + d *
    (108371549371731270650425666358328987207705319440384 + d *
    (-673191160396019985407073000843458522456820165378048))))))))))) + d ^ 12 *
    (1672548424580447222560767437618720879951846037520384 + d *
    (-3210564360440511941694799741020460774272242126946304 + d *
    (5333135061404150436683738922199137895276618227646464 + d *
    (-7991343219909117183620548922785143947252231359168512 + d *
    (11014193560414828827214763185314484896043740876505088 + d *
    (-14100021525388882054170247535071906926960301344030720 + d *
    (16832989955701466280977908045865486227274005308506112 + d *
    (-18725933197135184669519306740783583429519199247007744 + d *
    (19284715706227231929097111288782714403424971892981760 + d *
    (-18083872162240648329615118929014680220437155436560384 + d *
    (14840040770700682359472452705640516845556652661014528 + d *
    (-9469429969182661958834684172753924304488473324158976))))))))))) + d ^ 12 *
    (2118291886714084520584402744600266104239262507991040 + d *
    (6839619564248283695158609517458603308077386659266560 + d *
    (-16838569290680106166609881906156109791283575237115904 + d *
    (27183532792256493714253326411576784649353414848020480 + d *
    (-37129904166562131117778656574515476416878018721218560 + d *
    (45967844675657509064511534751506448910424954464370688 + d *
    (-53098986963078337178129593211203676175648925713432576 + d *
    (58095324704669214535920314275766237590399308092145664 + d *
    (-60733637921411992371128534838886610592946050274426880 + d *
    (61002965241401752630692156187900354312656853183758336 + d *
    (-59086694471290820565987391433503246677598469235146752 + d *
    (55324202537816052799513995714116549505722835673022464))))))))))) + d ^ 12 *
    (-50159234608024546542269179362252870383516231445512192 + d *
    (44083178181566062892310635026931839671960000167149568 + d *
    (-37581066175321487269525493896293306767667277357645824 + d *
    (31086716557630567461993463797018298360251983059484672 + d *
    (-24951218149904755655522281862078999273091146626367488 + d *
    (19426437105726258660374521712308691737231497205907456 + d *
    (-14662805976242248736538362732938435115451830176317440 + d *
    (10718761539357748600580372695911507757103523954163712 + d *
    (-7578068385381255561230112777450061458515485452926976 + d *
    (5170966469375942636491253915920641741690492150349824 + d *
    (-3395500576785278815869039549412803887268111644884992 + d *
    (2136294512720577187824437276484917684228159588270080))))))))))) + d ^ 12 *
    (-1279144109005784933718652354649015287184901669912576 + d *
    (720868912769562138603113442644590558181188020731904 + d *
    (-374706182368627270159489562702920390544683224793088 + d *
    (172069377593981728347028079685215037595604474396672 + d *
    (-61727580590153150887846910437085202117160420245504 + d *
    (7451212828846955862148836819181795088955964915712 + d *
    (15000927515631411886633225231910967749832594685952 + d *
    (-20921649147487155340090548311789712513095114686464 + d *
    (19338324382104576128307543306958472215117986004992 + d *
    (-15162845330085443506981211379112032512458231644160 + d *
    (10781698137952003695009927575880571332965817384960 + d *
    (-7148641685836147784752203208410294710312219181056))))))))))) + d ^ 12 *
    (4482667697453728120917392878284350914726380961792 + d *
    (-2679962603136098885245657526885163676980130611200 + d *
    (1535093441648042125412780075258601173385593225216 + d *
    (-845087507164862410147132949979367000143756525568 + d *
    (448004384139471887626411238584169230701157941248 + d *
    (-228979455987000499458499238834980148871201292288 + d *
    (112907965028312041857978575747919447022548025344 + d *
    (-53723280596403449608694876856322294218092969984 + d *
    (24663576918722709010808218638917050943670845440 + d *
    (-10919940084495759184492004642707265033274130432 + d *
    (4659612274732739470546974668123123026769215488 + d *
    (-1914353757751674757034297816563474531149676544))))))))))) + d ^ 12 *
    (756302428286998304090155871094632446000365568 + d *
    (-286880053886894520130821718225896065101201408 + d *
    (104286193913074065013204076239835757263978496 + d *
    (-36249731985310688561444974663896538663092224 + d *
    (12016485851334950448789294008309811621658624 + d *
    (-3786747405024433999966978849692098048819200 + d *
    (1130122745328568645654708134307005641261056 + d *
    (-317966725925879135815057100073160007745536 + d *
    (83877991450955744366411985658028723798016 + d * (-20606216093471310640557895778350008893440
    + d * (4674798835346672883859466108544307691520 + d *
    (-968686376687109777920182190491318616064))))))))))) + d ^ 12 *
    (180623946896816582558308610491081031680 + d * (-29651469063511151252098501662285758464 + d
    * (4135177099250938168823865343529713664 + d * (-456858680839315112965301633549074432 + d *
    (32849167623360673981350227232161792 + d * (63975256220369238261405541466112 + d *
    (-399681009942918552760544481509376 + d * (53554087534414994369600252542976 + d *
    (-2983789702777607462201395511296 + d * (365502421795597158637263388672 + d *
    (-215936411019203605137354391552 + d * (61649927212809773731575496704))))))))))) + d ^ 12 *
    (-9526058463890156356472930304 + d * (674350045626164878002618368 + d *
    (39855087096699415744217088 + d * (-14715064966230166612213760 + d *
    (1359390093404993126924288 + d * (-11222253907555405266944 + d * (-6829147834552701681664 +
    d * (216132488523932237824 + d * (12033890793015738368 + d * (4586109335151837184 + d *
    (-325254103937056768 + d * (-56208909601865728))))))))))) + d ^ 12 * (1586747000487936 + d *
    (344918589177856 + d * (16128644743168 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt6 (d : ℚ) : ℚ :=
  32354148704812314456716476416 + d * (-1181242355037628597210290585600 + d *
    (-7881122634655980546395124793344 + d * (29692765832624494060315978727424 + d *
    (42476589733207720658744896561152 + d * (-497741033790668534029177160696832 + d *
    (1284747189057171883408116212720640 + d * (228346812482978608087062140748288 + d *
    (-11982738978204368772894972725791368 + d * (40818967960346113167295488231884947 + d *
    (-58018413954828524245720899537521770 + d * (-69428985288767878743279416673715921)))))))))))
    + d ^ 12 * (610453561590718717857918832953133765 + d *
    (-1736112013218376199730005199069619376 + d * (2681687243388322285557334138492249623 + d *
    (-248471239080918676737449094642267594 + d * (-12272783009848160976861922356890771762 + d *
    (42590860450006385341983671903924425210 + d * (-88282857743615390011602461937872867702 + d *
    (113423816914806149973448503165192785352 + d * (-18339891591692771565820706096050765318 + d
    * (-373063535455229107572841092647309296151 + d * (1259114980293085678844304895458800854130
    + d * (-2675468354962338038683991199619519933960))))))))))) + d ^ 12 *
    (4138279965564766002459270046487145235753 + d * (-4161730697602456176036490891327233728320 +
    d * (-143968715716385558618036482948347827043 + d *
    (12990642044632562067549090846668749750856 + d * (-38795539051407314327158435847896685871543
    + d * (79503439818109839734466519892762051627647 + d *
    (-130120946442351457589212362938247132945395 + d *
    (172832220571670242058097781295788368325196 + d *
    (-170840147796900034557927553843015235992049 + d *
    (63778904608301847315122742443826867328283 + d * (233140910820904797151676367268589739923386
    + d * (-824416420276844947358138215379145504502899))))))))))) + d ^ 12 *
    (1823151563622105028351199813254154766540226 + d *
    (-3334291169591343189393398164049016681361155 + d *
    (5434548753690865328469558703637335682837598 + d *
    (-8152639575831887829318043116334288786761605 + d *
    (11453894373837656001297259489399986481429618 + d *
    (-15232828096587942044780080096399288585702221 + d *
    (19315874983349343684001220716220095000200871 + d *
    (-23474611789286365565558245610214551996566167 + d *
    (27447826770354423282668523119738925180469659 + d *
    (-30969188765985985488883982383960579218360609 + d *
    (33796341823061062488780437736712646411358401 + d *
    (-35737131910616635268425736007235095632600503))))))))))) + d ^ 12 *
    (36669316650196791568987614242365554074484247 + d *
    (-36551323379291630392328614081353982372980275 + d *
    (35423126586840256218083235821037913519401176 + d *
    (-33397818684521500888914379837721684029305903 + d *
    (30645700480519304685469391331133840438942301 + d *
    (-27373557313012000141010542864915821728261074 + d *
    (23802146777388305189809940244256010175941105 + d *
    (-20144819758331227061330024222007971056247546 + d *
    (16589702570279972146698341876658250524469281 + d *
    (-13287097258743250737129028698651826437237804 + d *
    (10342845931844147524007989393606065569373313 + d *
    (-7817499936310835235785798200651530973172655))))))))))) + d ^ 12 *
    (5730374129840480259400720387582168130631608 + d *
    (-4067056910882605639766226620682922936826811 + d *
    (2788740815788111921652079702837210041669376 + d *
    (-1841825440251153885379363214968142384390481 + d *
    (1166556984389234122648920996493872247990296 + d *
    (-703905908007993169629332359939398033864593 + d *
    (400340180379934877397292002338411306101327 + d *
    (-210540813003515810647890517389011689243907 + d *
    (98377901774499313176168981521434659904865 + d * (-36605369440961917060259216624458579478126
    + d * (5756695341075185753817532560534801154265 + d *
    (7334744441470803847620003041210012436652))))))))))) + d ^ 12 *
    (-11070476646810503792511122330953138287940 + d * (10471242176167581313665277967761939906405
    + d * (-8307449051210876169122466698861305223707 + d *
    (5949747254398078006501045551819919480792 + d * (-3963043091716254939856223043484387015338 +
    d * (2491887405394832596526399291065860492193 + d *
    (-1491537118053960387172442898624829284540 + d * (854143654735184996079573405070881372076 +
    d * (-469431177239931360600695306655731870930 + d * (248077901576346808974579613260883323407
    + d * (-126199118400223084592697172089699668301 + d *
    (61829436109448866053273977135950869101))))))))))) + d ^ 12 *
    (-29175692854259404160754036979661390342 + d * (13255005103702857342362879094984848302 + d *
    (-5793802250159060760304946230602292144 + d * (2433977304956320597589803484310556662 + d *
    (-981366046814911393948883404797476258 + d * (379085454040114571842671345552912535 + d *
    (-139985400658601695451810398598638978 + d * (49283812448619732589046691451704864 + d *
    (-16488595994749569287624301866600017 + d * (5221416688244275087838906768899486 + d *
    (-1557368228820990923905767434399033 + d * (434878321825258604321673296774975))))))))))) + d
    ^ 12 * (-112839644102300987301344361058288 + d * (26952799645911311716400642900241 + d *
    (-5856483149499814580916926368576 + d * (1139861916040631939827349503970 + d *
    (-194595661186418551936920607876 + d * (28263277434578787899720222159 + d *
    (-3325281127462806056086486962 + d * (289354349218039987402786784 + d *
    (-15120982529242926082048099 + d * (317829895240102981622509 + d * (-89488369491256149881115
    + d * (23360041664675776767423))))))))))) + d ^ 12 * (1352770127157719386603 + d *
    (-1723426009863529286750 + d * (413042161639364883390 + d * (-52182891400058288209 + d *
    (2983401949248487344 + d * (121629757920811362 + d * (-31123013487649442 + d *
    (1289817820114220 + d * (15725301564536 + d * (10322113924239 + d * (-647933439087 + d *
    (-175941338055))))))))))) + d ^ 12 * (4997392435 + d * (1233812612 + d * (58451635 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_6 (d : ℚ) :
    orderSevenSelectionPolynomial d 6 = selectionExpandedAt6 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 6 =
      selectionNumeratorAt6 d := by
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
      selectionNumeratorAt6
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 6 =
      selectionDenominatorAt6 d := by
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
      selectionDenominatorAt6
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt6 selectionDenominatorAt6 selectionExpandedAt6
  ring

private theorem selection_cofactor_eval_at_6 (d : ℚ) :
    (selectionCofactor d).eval 6 = selectionCofactorAt6 d := by
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
    selectionCofactorAt6
  simp
  ring

private theorem selection_factor_at_6 (d : ℚ) :
    selectionExpandedAt6 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 6 *
        selectionCofactorAt6 d := by
  unfold selectionExpandedAt6 orderSevenDualKernelPolynomial selectionCofactorAt6
  ring

theorem selectionEvalAt6 (d : ℚ) :
    Internal.SelectionEvalCertificate d 6 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_6, selection_cofactor_eval_at_6,
    selection_factor_at_6]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 6 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt6 d
#print axioms solution
