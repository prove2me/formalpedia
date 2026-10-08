-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_17
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:12:40.255427+00:00
-- url     : https://prove2.me/submissions/f2b84aae-5b87-4562-ae97-b3914e7c35f8

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval3.At17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 17

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt17 (d : ℚ) : ℚ :=
  -1067161864863371264 + d * (-234350710455892992 + d * (596911664774260992 + d *
    (-1307550009337528640 + d * (1846479046837231488 + d * (-1010806050299714688 + d *
    (-637560899559329856 + d * (1988290878017335104 + d * (-2720779483863274560 + d *
    (2688224287373516992 + d * (-1799560450393062720 + d * (553141091122004736))))))))))) + d ^
    12 * (571121680395755072 + d * (-1400531618985655488 + d * (1861402879931753088 + d *
    (-1934769335475496704 + d * (1727352365025118848 + d * (-1385476496419322496 + d *
    (1013546062861063168 + d * (-680209059766013760 + d * (423370446978108288 + d *
    (-246324233032086912 + d * (133078701825552576 + d * (-66070229764908480))))))))))) + d ^ 12
    * (30290808044266944 + d * (-13011236044736832 + d * (5192729599610304 + d *
    (-1849498191974336 + d * (575683757150400 + d * (-170360090133312 + d * (56424405163200 + d
    * (-19778513843904 + d * (5710989834432 + d * (-1187097446208 + d * (232133321664 + d *
    (-79365936192))))))))))) + d ^ 12 * (27478352064 + d * (-5263091520 + d * (397281600 + d *
    (-65924800 + d * (48836160 + d * (-10597056 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt17 (d : ℚ) : ℚ :=
  -1264697011204966080 + d * (-300570781711606464 + d * (900615745763437184 + d *
    (-2098792841429410176 + d * (3258141850993568448 + d * (-2724248029098557504 + d *
    (871785328288900096 + d * (878673296817041152 + d * (-2238226696329700096 + d *
    (3140604688572139072 + d * (-3083145261235140352 + d * (2292850182313180800))))))))))) + d ^
    12 * (-1280972747586274752 + d * (297081828788044480 + d * (466728284513950208 + d *
    (-843974671702625280 + d * (882948484478822464 + d * (-746854367878387072 + d *
    (556306685867637632 + d * (-378039707000175360 + d * (243732212277094656 + d *
    (-153574691573075072 + d * (94152873197924096 + d * (-55413264406114560))))))))))) + d ^ 12
    * (31466602372976064 + d * (-17386132123536064 + d * (9271449537995648 + d *
    (-4710651194061440 + d * (2272282949179456 + d * (-1037796074681792 + d * (443753394442752 +
    d * (-175836402781952 + d * (64639830400320 + d * (-22031115361664 + d * (6763353206144 + d
    * (-1751348330496))))))))))) + d ^ 12 * (347474151424 + d * (-44896924160 + d * (1992001536
    + d * (384430080 + d * (-52670464 + d * (-1343488 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt17 (d : ℚ) : ℚ :=
  250312693562031059407019556816167556974159677853794304 + d *
    (-11437186801386543681093122640806211555337314688204537856 + d *
    (520204477901067383823969450646964188410930385451483136 + d *
    (36007366856747257888989024174220130963108106475802722304 + d *
    (-70738463295656419758031458678869566330307705720381112320 + d *
    (78068123758235977160760148624623080818140732653117898752 + d *
    (37857890280598650352871317787514057955047970730478403584 + d *
    (-298658027641151595967977509177938418175661609351050690560 + d *
    (552074058288604859288419933987448132112217934430190436352 + d *
    (-553449670479085349003412333450344334250505194299474837504 + d *
    (67254874444032901596062267829633015624216127858214961152 + d *
    (941644393696929852696326017769425852347366650818877194240))))))))))) + d ^ 12 *
    (-2082942665548713102548965613285307363404732410877866672128 + d *
    (2620223166289495003722507014151449633005062114672587309056 + d *
    (-1833107135583181119541068730215341512986563151163878277120 + d *
    (-567321927407230306312066672535538368120944068077772865536 + d *
    (4088188379953538822241525118838841855302353015939356688384 + d *
    (-7426007712913694026752512971768692282072748414875150319616 + d *
    (8925625676346277617112710373587979058951891828517876269056 + d *
    (-7304156994570842152550778694276918830120234463186961039360 + d *
    (2299856664641662760477432760068887401805489529088277217280 + d *
    (5023994049481746417746174564032628181929921661544749596672 + d *
    (-12519907125908514509106157662213190217305464270932141146112 + d *
    (17693604812058423962346205981054164049771919872381811425280))))))))))) + d ^ 12 *
    (-18611364330365160358565049026605848192801020077317094899712 + d *
    (14607190947892238508084503279416854816435365970714403274752 + d *
    (-6532117677344477415686969835569220918415373490846339170304 + d *
    (-3540581624519727044910227954559319795374329308981431894016 + d *
    (13017167128105008238713348899850489064604664908909892075520 + d *
    (-19598116705385429727599742992746309034369764317044118650880 + d *
    (21914383639853848719557282871061527511292337708142266417152 + d *
    (-19803536341280533988569204311395831588392856642042736148480 + d *
    (14190601589613507000867063407991516775800266074423132946432 + d *
    (-6677981137642732723297911321386419174396672525277455974400 + d *
    (-973496052185796388891948829370299959173610404825221824512 + d *
    (7297943938489697841713568840541605317923081396389483642880))))))))))) + d ^ 12 *
    (-11400933896265678810643590043828184357284029401811559907328 + d *
    (13027469313919961925501667410280889466391560474018955395072 + d *
    (-12458421171766538822775551565085718472684991921701433376768 + d *
    (10310640577287507681284190542960573655857570243815098023936 + d *
    (-7319065844093398348242244220155200993553354481120897400832 + d *
    (4158612423891725528461706161629842517351156824022794371072 + d *
    (-1334529310661540725211699405395190803408520950369777614848 + d *
    (-856814416338684694423678200294267376942285123455427543040 + d *
    (2312489535426031321038776508771715753322125790625126678528 + d *
    (-3075649709386897706350307303412387204099338959370266869760 + d *
    (3277620248829021601366919013673904335821562555020733054976 + d *
    (-3084961266350063933429899001671289032532061317653572616192))))))))))) + d ^ 12 *
    (2659967280631696299114329889780177487756623224860498460672 + d *
    (-2136933285870970117922348708905477399741012326250450518016 + d *
    (1612395086315543485505875223447127625431437930826559651840 + d *
    (-1145526960554150666772748934789935064186655849357635223552 + d *
    (764483409348272932453597145162843563644179403635858341888 + d *
    (-475095378726840279740241931141217374411069133977056444416 + d *
    (269414750285134405087865710597131772202769606889854992384 + d *
    (-132715574747746432561691378933934592194858698434754379776 + d *
    (48456780157817084589876269157029132445190616346102595584 + d *
    (-1301303046441642265965123774035603761729878415028256768 + d *
    (-21411303963649352436813612382744384571520852312474779648 + d *
    (29256591029370917099894811211554506309536235387492237312))))))))))) + d ^ 12 *
    (-28945119440625194653798970534419235904815770104102912000 + d *
    (24838244197229120976644133085150433053930601148483895296 + d *
    (-19539923292399276461242518737738315423631781162327736320 + d *
    (14440001363277524795258156680495968393203638074097270784 + d *
    (-10153465668693026473683865008876213829705092219449901056 + d *
    (6843831207853932332257275059320512166550894152514797568 + d *
    (-4442418482484245111067810600755492105816093087878610944 + d *
    (2785094668398504200354705192745737343444319590825590784 + d *
    (-1689476203252642400948140560365990348146109987981623296 + d *
    (992685835615360582427562818028942688164623784406679552 + d *
    (-565214111763185588610309589455513614453789232938090496 + d *
    (311830754042943440494495123500817010919554594842607616))))))))))) + d ^ 12 *
    (-166595149955029947010958944843027631840436332017221632 + d *
    (86082082287507305352711449233784413823961954953723904 + d *
    (-42934030171287573114404270429930993378235841108246528 + d *
    (20605303900811567329087742505514834396937489027170304 + d *
    (-9469837841091856723927972210809283058908967294730240 + d *
    (4135235112139425539385888258535849678290092642795520 + d *
    (-1692767945070444217455552798454733799247967478611968 + d *
    (632912658471930285650924804547663400594307436249088 + d *
    (-203429508987426627029650953800337747419016637710336 + d *
    (45581455864364654022157482973359835789635329982464 + d *
    (3419460466895164869203717008884275707369460596736 + d *
    (-13180274874515502324875484015465964267607890591744))))))))))) + d ^ 12 *
    (11248020947423102908643912894701903879365884116992 + d *
    (-7339092310857838942305714539535408480007145390080 + d *
    (4210741578002214348733124716807300903739468808192 + d *
    (-2225931590892499700481978812137326499328742653952 + d *
    (1107466251933890324409710128146733558917040963584 + d *
    (-524476094698176393837724703046391435702587097088 + d *
    (237985884811696505147593210354237685670896992256 + d *
    (-103881817620699967831873941256659733215570034688 + d *
    (43726715529601573659669903836172505058005483520 + d *
    (-17773982720963241930389430292083981647619555328 + d *
    (6981479976875104399843196130955381013201813504 + d *
    (-2650224227528915273364419075956624193623949312))))))))))) + d ^ 12 *
    (971917898969571297699990411467757637074681856 + d *
    (-344064842235816970898729270766774665445113856 + d *
    (117432380204559840638787443508695812130471936 + d *
    (-38580094397638616363785304664093693247750144 + d *
    (12174641882405074113831312673981106144935936 + d *
    (-3680575084948318372462495005821574927876096 + d *
    (1062406003367094486845644349742877374414848 + d *
    (-291574664633172801468956680050884696604672 + d *
    (75679948024110159795259395576363507777536 + d * (-18452245178648850516328545713893725962240
    + d * (4189720175058288121999179283889484464128 + d *
    (-875838920188963130652648435400403058688))))))))))) + d ^ 12 *
    (165941853410718019894447348188090990592 + d * (-27848554951721337801535411955716325376 + d
    * (3987523001572857329593886540658376704 + d * (-452579936475121691806866176271712256 + d *
    (32886755382660215906573940246446080 + d * (358258502887708294784998108561408 + d *
    (-510433432167430724183990140665856 + d * (72935983620429947861139685638144 + d *
    (-4429841279782099389391995404288 + d * (228323513748083673655416979456 + d *
    (-165261000915965338483865157632 + d * (55957030242669055765880242176))))))))))) + d ^ 12 *
    (-9405074249790567117436223488 + d * (714343208654492964685086720 + d *
    (36424502069782005875736576 + d * (-14812094799614426945421312 + d *
    (1366030947213790886494208 + d * (-8217155964164412014592 + d * (-6867165123351671472128 + d
    * (178208933160675704832 + d * (11808154653819928576 + d * (4797732975946498048 + d *
    (-311858857458532352 + d * (-55701969029300224))))))))))) + d ^ 12 * (1601251647160320 + d *
    (345076148207616 + d * (16128702414848 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt17 (d : ℚ) : ℚ :=
  24765078913875779330375273940335962610710463 + d *
    (-1127113239278063889133162621029409197092155729 + d *
    (-159405497631206686342574478789489117584816775 + d *
    (3934580523174520380388369976317608250932838589 + d *
    (-6511867514252915615949596926908883464273076812 + d *
    (5144115423669270763115665876663673994350683929 + d *
    (8073992249137773938762802819016805349307109021 + d *
    (-31628886263061803823460662006688267422684555730 + d *
    (46897012682121664935678766523775505809757624920 + d *
    (-31954307226618088910388933741812548851994672052 + d *
    (-24972383467184960610361931423484768818248384288 + d *
    (111388476338942729109199074398643277319720557883))))))))))) + d ^ 12 *
    (-180405444927348892446586418699733668735617730832 + d *
    (171298074413764725385976390355757460309570615426 + d *
    (-48316117666573361373729417534479545959476604807 + d *
    (-172728701697016828798320501854287167151365625702 + d *
    (417212689149014239380820040207305695483775442660 + d *
    (-573051165433349067301470354729989861195092380350 + d *
    (540825460649369246928439698333913164999527203613 + d *
    (-283768473205659470155599139652133076176910833159 + d *
    (-148859426503102901210725396064266710484238449935 + d *
    (632201943295803279285063946289040519035129217723 + d *
    (-1008396758551841659218033604874729033067179913781 + d *
    (1145655337376343132751788196112078302242628271336))))))))))) + d ^ 12 *
    (-986324567506259609039334553795667006794223755678 + d *
    (565023610575340037202247523045788881227280922086 + d *
    (6233850346447779011542220495357915233753322473 + d *
    (-578025703760414591060863810730996755589917460225 + d *
    (1012059922069024428964573503828129982136955069117 + d *
    (-1219592766106819210252827910678041969877566260447 + d *
    (1178643917033369811022736563469414917915779553042 + d *
    (-928979654367375892126063200008662546809896055537 + d *
    (550862559987408805141973886381500095089319296465 + d *
    (-137349514331350097285469471402719466171451045131 + d *
    (-230211699401757903741475355148142672060148370284 + d *
    (497553770102452332558109614790310848237723342864))))))))))) + d ^ 12 *
    (-642305479689013901292613347164624416381359371650 + d *
    (670108145920336628954472170199084228776076348792 + d *
    (-605624434993114379449965892893009605131556486347 + d *
    (482238437539629687436619882048046563063718416090 + d *
    (-333252822184326743700413712671205885020706393731 + d *
    (185992984268081852013480910274746474768972381441 + d *
    (-59045864630008080466027870504961376273278593525 + d *
    (-37919469624076611235539682358589223193764885929 + d *
    (102661224553371192754011579665604172260675393654 + d *
    (-138115693326469308813464812716765889180806809217 + d *
    (150094850153452170560138961326018035075658565817 + d *
    (-145369980352201571759741791804513481107626282593))))))))))) + d ^ 12 *
    (130333803253667039840689755200216260668663495726 + d *
    (-110245840532285271108314736908618089400730904913 + d *
    (88954307042226138451042905791144825632965410551 + d *
    (-68944888146827696177676033077601854973511528118 + d *
    (51571039217270937512322946009977039337369263733 + d *
    (-37350705878212795814802993720228304669232264305 + d *
    (26253532440491270929982081513213844565296653668 + d *
    (-17938516208928795326374125148512250811158196900 + d *
    (11928651654711984420725202485677836473717495310 + d *
    (-7725561601901990006105104440883605324211422059 + d *
    (4875221609592783033044072621773324397527065574 + d *
    (-2998200994001812097403717088521838906469882975))))))))))) + d ^ 12 *
    (1796811937424174204764819176549681488039405133 + d *
    (-1049047264031888507581636848001850738202628110 + d *
    (596364283702067483862024409497313791921671369 + d *
    (-329846733734434233837075458704179109590840403 + d *
    (177304020605726077974771111282327378906293309 + d *
    (-92485315069398959600497962952564194293415704 + d *
    (46716125101855769352978512702070886859701653 + d *
    (-22783696972487891500759981660114605793007255 + d *
    (10682946440242581884602219697617159543140360 + d *
    (-4784575858949234734277117800655681827441295 + d *
    (2025250433064370095749805026287465737336877 + d *
    (-794920297572235004147104465782235328725167))))))))))) + d ^ 12 *
    (278014088677543202554658143678184528269506 + d *
    (-77643382744959771477600356587487455256944 + d * (9168153334900831123278185923468581606695
    + d * (8885233097967126348150433187267054804531 + d *
    (-10156696537862046999253637977979776069740 + d * (7307972662859089043737256296395657780997
    + d * (-4426726714788229324947143592111429039808 + d *
    (2429404840807602300227357871803383929802 + d * (-1244440543676496404818064293909324533961 +
    d * (603893016037508312677922321520178869931 + d * (-279942552789289540858393429502671237243
    + d * (124578855040900125622933413012717154708))))))))))) + d ^ 12 *
    (-53379462868151797566352664771282613896 + d * (22059600321203359862768304565773851603 + d *
    (-8799817583929747458398879853540736390 + d * (3389045729411018731613672822082832011 + d *
    (-1259646383496065652134139458441541552 + d * (451445050292603144680291957739816361 + d *
    (-155788229370379147816302742496331864 + d * (51663862637330018574474438929125757 + d *
    (-16423387184866829828323738724660284 + d * (4988721062409109699129944442358826 + d *
    (-1442227382710481574721877726343883 + d * (394750873965889188702866579712622))))))))))) + d
    ^ 12 * (-101570380373571174854610120183363 + d * (24329075446620606321731090235838 + d *
    (-5353659397842692350105638286658 + d * (1063259192626673965777587679013 + d *
    (-186048449102261886553150083020 + d * (27702813014697367673662944448 + d *
    (-3316607820306726526901935170 + d * (284251220525755175947360724 + d *
    (-11800337983285522019247135 + d * (-508457108368142415031576 + d * (21862189139445497666120
    + d * (17338580039919916788221))))))))))) + d ^ 12 * (692637014810883788660 + d *
    (-1570857995926250144592 + d * (403832127842918975184 + d * (-52488936453059641193 + d *
    (3009374662861545039 + d * (127396652519886411 + d * (-31083523031519031 + d *
    (1190150433784918 + d * (14623757759955 + d * (10984403064081 + d * (-603709433283 + d *
    (-174278270033))))))))))) + d ^ 12 * (5046309193 + d * (1234371412 + d * (58451932 + d *
    (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_17 (d : ℚ) :
    orderSevenSelectionPolynomial d 17 = selectionExpandedAt17 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 17 =
      selectionNumeratorAt17 d := by
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
      selectionNumeratorAt17
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 17 =
      selectionDenominatorAt17 d := by
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
      selectionDenominatorAt17
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt17 selectionDenominatorAt17 selectionExpandedAt17
  ring

private theorem selection_cofactor_eval_at_17 (d : ℚ) :
    (selectionCofactor d).eval 17 = selectionCofactorAt17 d := by
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
    selectionCofactorAt17
  simp
  ring

private theorem selection_factor_at_17 (d : ℚ) :
    selectionExpandedAt17 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 17 *
        selectionCofactorAt17 d := by
  unfold selectionExpandedAt17 orderSevenDualKernelPolynomial selectionCofactorAt17
  ring

theorem selectionEvalAt17 (d : ℚ) :
    Internal.SelectionEvalCertificate d 17 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_17, selection_cofactor_eval_at_17,
    selection_factor_at_17]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 17 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt17 d
#print axioms solution
