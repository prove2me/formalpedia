-- Prove2me | solution 1 for MazurTransfer.order49_selection_evaluation_33
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:55:05.710461+00:00
-- url     : https://prove2.me/submissions/3c382900-ca58-4678-b5bd-770d66f8c487

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval6.At33. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Selection-factor evaluation at 33

This shard verifies one independent rational abscissa.
-/



open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private def selectionNumeratorAt33 (d : ℚ) : ℚ :=
  -2970335001724992000000 + d * (-260213645058871680000 + d * (302795087072284857600 + d *
    (-674716809563875457344 + d * (1268321267721867152256 + d * (-850580487217837345920 + d *
    (163948827740113887168 + d * (134540203433502707520 + d * (-231456933347456193600 + d *
    (279385621170634080448 + d * (-207036176318447654208 + d * (111692379675306836736)))))))))))
    + d ^ 12 * (-52981006995000641984 + d * (16517778186393842496 + d * (7795488091950197376 + d
    * (-16623020820479960832 + d * (15472145535953015424 + d * (-11766335531116071552 + d *
    (7982130202899810304 + d * (-4779415065064974144 + d * (2600312949143859072 + d *
    (-1351876743985984896 + d * (661160751906920640 + d * (-289443136742540736))))))))))) + d ^
    12 * (114534269677448640 + d * (-44257219041777984 + d * (16944468143968704 + d *
    (-5744881996289984 + d * (1565620812432576 + d * (-379355121693504 + d * (116942167274688 +
    d * (-42532292003520 + d * (11714321252544 + d * (-1965796362048 + d * (281744834496 + d *
    (-110070643776))))))))))) + d ^ 12 * (41051372736 + d * (-6981764928 + d * (293804352 + d *
    (-31530688 + d * (51121728 + d * (-10560192 + d * (326592 + d * (122496 + d * (5184 + d *
    (64))))))))))))

private def selectionDenominatorAt33 (d : ℚ) : ℚ :=
  -3520331141649396693696 + d * (-324790864934101384896 + d * (486541687818617456256 + d *
    (-1114902969801702829440 + d * (2000421906642193043136 + d * (-1580682583024410406976 + d *
    (688309353070637457408 + d * (-243525893171486516480 + d * (35238384762720899328 + d *
    (173586910855021853248 + d * (-219098605804213203712 + d * (163930921748937349760)))))))))))
    + d ^ 12 * (-107249272488314102208 + d * (61137901356491489984 + d * (-22058918666763917824
    + d * (1381279967216906240 + d * (3900194547542100032 + d * (-3929655268786851200 + d *
    (3014643965754043264 + d * (-1900519711398660864 + d * (1043975091920232704 + d *
    (-579727186333060224 + d * (323315258792576768 + d * (-162734593158482176))))))))))) + d ^
    12 * (74891040220649920 + d * (-35210891197822656 + d * (16994030861401984 + d *
    (-7674686631476864 + d * (3188730861216832 + d * (-1290854012784064 + d * (512901417162240 +
    d * (-188014960589568 + d * (62179728612672 + d * (-19523201244544 + d * (5993453776256 + d
    * (-1644336209920))))))))))) + d ^ 12 * (346310813696 + d * (-46011642368 + d * (1966983168
    + d * (406679552 + d * (-50425856 + d * (-1327104 + d * (144384 + d * (83968 + d *
    (6144)))))))))))

private def selectionExpandedAt33 (d : ℚ) : ℚ :=
  5410319529786015134332275931632294782674033549562271473918017536 + d *
    (-252162193363501336132526888737512002937471482036390995388490842112 + d *
    (157284164068279970513924896211280106579742327430237177189548163072 + d *
    (193952472438587871602130310139236016965301032676181641333516009472 + d *
    (-330976856802946892183222353939041077960383525341288351142067306496 + d *
    (557093905662596933589385770433371843816058010778514562598323355648 + d *
    (-463270177017593147448308212500301878677818375845823577125559205888 + d *
    (-28732161498552098306265072868248479437627967919653722551481270272 + d *
    (475196007537945133308515001772272271695521452612307576685656801280 + d *
    (-705531767143952783455231565426873114518821283212863872897967980544 + d *
    (688866664619955752140170735850063782458306369075782177968199565312 + d *
    (-375940792513029164362740301416001817445021693240666810056989999104))))))))))) + d ^ 12 *
    (-68753729740476093070146839996350716509601867363162445375308038144 + d *
    (403228232617238283724630385485305734727544445875118493347845242880 + d *
    (-539676743594236878410073711303648190374030533938359896828641017856 + d *
    (478638977436521098695044717693323785453129116204919227154493865984 + d *
    (-268819348985246624709778622435414274872928722877127869959944273920 + d *
    (17385160316291707536910852236374466238891145452850324847555510272 + d *
    (177514080772258798872386231331050193291703219221897672710067060736 + d *
    (-275341753496620797408385070781464552206210830090098447681850966016 + d *
    (277529020924002651835545263568383552757752784951960295851221319680 + d *
    (-210892132778237146566617424682823121623996652648753652417168146432 + d *
    (116348726952439617823567751436017040699717914493901665283026452480 + d *
    (-29308424096115035514463786339923600122584869544912454258170003456))))))))))) + d ^ 12 *
    (-31375873500665374961906243615538971238870605438669748776141324288 + d *
    (61231580855179942754475538957756243295113287564134569057376534528 + d *
    (-65317945163058963832280720317970838570715421870068503645083926528 + d *
    (53547907960045347635901952041260316094061055417390052032514097152 + d *
    (-35739218184475841431851350298842184469603251591133241463507517440 + d *
    (18702354927352239143373010244659109483707373638491993495897899008 + d *
    (-5902140428809047818291646721959254811109146837746604393877471232 + d *
    (-1817798919187827864187749289742293225770602685872986626534408192 + d *
    (5252431816673344774214285500757442184279019683135118111297503232 + d *
    (-5828362792751092519016284920314465051844522421278242315392778240 + d *
    (4901253495165043839145043433106395772349053098363653352499445760 + d *
    (-3462389779565693097389079109347604804092775211392142189353500672))))))))))) + d ^ 12 *
    (2097197445954827838312919551006873551943776496732489712268738560 + d *
    (-1058578216463185448790031047348949150315286920250577070507687936 + d *
    (386170814936025619879258131589842265077825694332321677917028352 + d *
    (-16538183596019882202375922820752262766963888369599373208977408 + d *
    (-144230113592084529165260266243278927326860716318039726154055680 + d *
    (182351747145416267734603538320273066830722098406618614257156096 + d *
    (-161135631818921360527585774212907064833239152571310779470708736 + d *
    (119808020231393632808296828650897128936651796530027979671339008 + d *
    (-78871045298403158729749655524621505507311208231604449925660672 + d *
    (46624825140414432205958761349919943701675058882114132457816064 + d *
    (-24550340832436262240080622709738544678904387276700595091931136 + d *
    (11053550332428512202499813659695564189939695600858880698482688))))))))))) + d ^ 12 *
    (-3678955954478281220725152240652205048885714001003969678934016 + d *
    (172241898552255073231613842922314103584119501693264016703488 + d *
    (1152593280827709398691766321429255981738510897747864011931648 + d *
    (-1395462825688478834174342672513636131716952222645725040476160 + d *
    (1194272286298188940581914245306804011388189133268922066272256 + d *
    (-876320968315022971550088789594951881463913867624110361149440 + d *
    (584152738239909279978128509941964725249371948351323975974912 + d *
    (-362643395700067715946149218270409391591551048992825309921280 + d *
    (212222382498572867469263603010568324296298986157712712663040 + d *
    (-117742226472167267246862752136872245467387262222319518482432 + d *
    (62020845475788866719714924331277803129824017372756529381376 + d *
    (-30941500133007124833572315954072366065106554798134724395008))))))))))) + d ^ 12 *
    (14509065626083881462798337908584246013206852967948425887744 + d *
    (-6289627224210638636845997794836721715256981881777773084672 + d *
    (2428654902732878664375444246422381269306861427028692828160 + d *
    (-753072175953393317209576235686013876547325388067395338240 + d *
    (105564265735808968424145579878217784263552328595433586688 + d *
    (95409188844138271666917383258044233751080441461632925696 + d *
    (-123779882233479445836578225138705071320878723768603377664 + d *
    (98604992079478370109070070780003759267191575227398356992 + d *
    (-65886938369000101597481604876310381667807238238665965568 + d *
    (39865200492190734043193918755154723798728208688833888256 + d *
    (-22523342052334980920932802069304107330769363957664972800 + d *
    (12066007783116773216462173881703301187043869695124176896))))))))))) + d ^ 12 *
    (-6181786030946170419564841346005576478254471967075991552 + d *
    (3044437504676170317934257759560044108510292113340497920 + d *
    (-1445740109876837360229290587269522444870023011787866112 + d *
    (663212730450815949633138296883117209030497300409483264 + d *
    (-294161719455442890166421516960661334804322333274931200 + d *
    (126165939069869193860912075831944277889268431301640192 + d *
    (-52291606521312702026941583799538927525616510576361472 + d *
    (20911548206037953929944750544910006881497505882963968 + d *
    (-8047360488670999956163075313305090874821517524598784 + d *
    (2967334370865854359258153500796369625216324796416000 + d *
    (-1040983555472440459801390474413020433381727840763904 + d *
    (343182420859960817603843344972347026725765717688320))))))))))) + d ^ 12 *
    (-103841245328834935485398127830835073022106931822592 + d *
    (27339897748197007232356209982445055366550618636288 + d *
    (-5277215196699279858499302500348385681950216814592 + d *
    (-12546443695246163653220893010438048873866854400 + d *
    (753444157081150480692544400904293181566265589760 + d *
    (-546977108624130060371397563858672893741042499584 + d *
    (292310188176383196614643554467365647410029920256 + d *
    (-136040259462210414239213875067429315047280869376 + d *
    (58109573354533977815901030517709661075772801024 + d *
    (-23313267885070615051262824093495014154873077760 + d *
    (8890577020816130280178698423846803690250043392 + d *
    (-3244736350337113059480357393183018347997691904))))))))))) + d ^ 12 *
    (1137823952809941058951857643004135087550496768 + d *
    (-384197074460726156466965128100958229203779584 + d *
    (125023356785346365874237832953916148872642560 + d *
    (-39206266369847835277557618343129745605787648 + d *
    (11839364560707828525574292015385426039144448 + d *
    (-3438318804882361554552719326803859296747520 + d *
    (958389907528969798537317429374872814878720 + d *
    (-255637287746519046259928830659473836605440 + d *
    (64975843513234048806473621456933554225152 + d * (-15647151750416999424104660300580900044800
    + d * (3542969820957432867160665276835472867328 + d *
    (-746508292835218486244190591111011500032))))))))))) + d ^ 12 *
    (144183879681801506958885824336340189184 + d * (-24944191412267215094403952359721664512 + d
    * (3718384163576472561792970332923494400 + d * (-442393102661665640635349321019031552 + d *
    (33597523156853875386828233193291776 + d * (549980617887568691853354888855552 + d *
    (-640546230165051763524501540962304 + d * (100071073246119546838728295055360 + d *
    (-6807165530414852806991103655936 + d * (67808205300268254798958034944 + d *
    (-91936709336829302417279942656 + d * (47430280478200817532272640000))))))))))) + d ^ 12 *
    (-9233575165884595750989987840 + d * (775550276930335185966989312 + d *
    (31560987508843929294864384 + d * (-14989395951165415129088000 + d *
    (1374173527804172750815232 + d * (-3659066406882854567936 + d * (-6905033051994233503744 + d
    * (123796749532566913024 + d * (11501629254551994368 + d * (5105826579590152192 + d *
    (-292374335079841792 + d * (-54964600923750400))))))))))) + d ^ 12 * (1622349315047424 + d *
    (345305324978176 + d * (16128786300928 + d * (579044114432 + d * (16752574464 + d *
    (139722752 + d * (-262144)))))))))))))))))

private def selectionCofactorAt33 (d : ℚ) : ℚ :=
  77287908104241163862319454070337497614227951209775087 + d *
    (-3595115277962563449503228564373469994578066827230107953 + d *
    (1903001896447721925523522867673888127502399736131925721 + d *
    (3606584619546827563881151037930000021763163456834528317 + d *
    (-5236954448768311337692285876374515073429162082601266956 + d *
    (7194325433502861810096972690097875432731814642454845129 + d *
    (-4449585538067448827962509554369440969793069028897584115 + d *
    (-3097694650239063738024680667303259576800994888442512578 + d *
    (8402948105529838757590009634337095956584249290784858072 + d *
    (-9339008159779022713969492137243950366495633514369064388 + d *
    (6791738708701474188664275282038767272864276270248423216 + d *
    (-1451558620220535879488111256623790655865778424436388757))))))))))) + d ^ 12 *
    (-3942915896258468148873886465244478610116334429453798640 + d *
    (6573160360875062165870984781020604043975521288522693346 + d *
    (-6284608855856669731154071141552245728451146237813021175 + d *
    (4070461062953836409501936127158590448143708647379620762 + d *
    (-1018716465086354534277484286660330532665604679457225708 + d *
    (-1617471192703707804947536438294560445553797031548546382 + d *
    (3041692317157868847493676351479976738674574263541212573 + d *
    (-3244626193861208880848316794150283188431638956159504199 + d *
    (2592565160362877716846958453300367258395665278077536577 + d *
    (-1533601593341914643870439896922174446509610600775251141 + d *
    (499009109726353112931234807162198115744363367730360875 + d *
    (240618959681639806114291633591259919115108166756303288))))))))))) + d ^ 12 *
    (-621606692481835353922326669378410189336181324210604142 + d *
    (704582884015605208839760604584915074344675534058520310 + d *
    (-597318099574089960720991964673838282484898578206911303 + d *
    (410981688737950532979685205963667401938309314900619823 + d *
    (-227020084832275120228762588179030227416438339638314163 + d *
    (85990358351292959672231738732453479732742648059710225 + d *
    (2161657615971283941505110941384716345087393927521106 + d *
    (-44554604299716088673566497310831323234066283522673089 + d *
    (55497058736941376995288015224461810343026657602882609 + d *
    (-49297104187739991431583481526960912127716539130147611 + d *
    (36490123087698643860424057766867062456828454391017428 + d *
    (-23358026007239167658493863892919357372901029247573904))))))))))) + d ^ 12 *
    (12848458237352992849145852901651691187188399234565086 + d *
    (-5701480171507464476663684574529758301554154226840424 + d *
    (1494691855254088318336857951976500016573877526480405 + d *
    (587073911465894584361847137936624602489388145865930 + d *
    (-1340863553872474385342605464443572393690203487692611 + d *
    (1385396135078026859243538988366986529926541394442177 + d *
    (-1129099830482851847332308279597183360092655548531621 + d *
    (802644940181987233152496437758979416339127295165527 + d *
    (-514266879866081271749824352213815159860576550406490 + d *
    (299669707147024068985409000096225253932665924417887 + d *
    (-157599977103389832776940711699982964733551795780503 + d *
    (72343737953937145514296098590589651788767221791279))))))))))) + d ^ 12 *
    (-25992524210359199412356179286788260661931476289138 + d *
    (3653070350664961936919054226871631358467399201311 + d *
    (5257654495798055747583779088572499250301135036279 + d *
    (-7449498100717502919504184836692351579586348546390 + d *
    (6765711820260213276845799340673863885040060083109 + d *
    (-5188656440447582566419715174782307187544282916129 + d *
    (3612117692211720748751982925822899026219307012548 + d *
    (-2352733982298260186878609000710846111157230790292 + d *
    (1456321249425631389074815059648451566940988556990 + d *
    (-864468671550697844441174803071231451013860832331 + d *
    (494919845754008737640127508953444385107895421206 + d *
    (-274320616081266865072540490087807956262297370831))))))))))) + d ^ 12 *
    (147575345992968905883122288538181905381768607133 + d *
    (-77183951996807505022716007610956536986696674014 + d *
    (39290030008129322369171386745386030719376253049 + d *
    (-19479776515962465912765648043993514093729075619 + d *
    (9409740873033839662025707496718170725525138413 + d *
    (-4428671110262030082678373932450650168662047368 + d *
    (2030335894271294861296223428969117106758589461 + d *
    (-906237401477511233045261273616448324168794599 + d *
    (393493244092457297138195564719945721868631832 + d *
    (-166009703238806990259729979374661869913454975 + d *
    (67938427520518094187762753458277615668859437 + d *
    (-26908177171212485710582933187826165836505887))))))))))) + d ^ 12 *
    (10279710733598505610115196843879967755108818 + d *
    (-3768838381573379626811994076034273774628704 + d *
    (1315637025335490154241413852829242281811559 + d *
    (-431533206131966092949140614561630667678061 + d *
    (129691609067205295254821358038820590596404 + d *
    (-33699958769699288777999908838382828745547 + d * (6229109073519327089946552185722605017328
    + d * (237135312745064724318182697204257013514 + d *
    (-1060272950545540896882271949539822891721 + d * (742230263921340234214942245511537532987 +
    d * (-392592721799318476504764349439017433211 + d *
    (182101272116853489472042317217043387780))))))))))) + d ^ 12 *
    (-77757406413896824534243297381174748984 + d * (31234993513335422284735282626065180371 + d *
    (-11936758031530755146051919297427763398 + d * (4367077344270570457125094645403368731 + d *
    (-1535039934959228415453215229750434816 + d * (519494205876469642731729285823440745 + d *
    (-169440852045256747916729370594939160 + d * (53259569809822568435332908129822717 + d *
    (-16111784257604886931894061533478524 + d * (4679693501738999719638947584455226 + d *
    (-1301261300242635145506756411961259 + d * (345371281600083753139538742874958))))))))))) + d
    ^ 12 * (-87170581547373178704783422730355 + d * (20788780008966926525208491242158 + d *
    (-4629600591223117092403766870338 + d * (944287206275231189635178703557 + d *
    (-171432714694634688042354712396 + d * (26578774390069715349288818576 + d *
    (-3290370796503788046653857314 + d * (280596386247239912565082820 + d *
    (-7829554049254795705510879 + d * (-1643901218269145821572872 + d *
    (185876630999931379133400 + d * (7948611631361559111933))))))))))) + d ^ 12 *
    (-274918478103445893308 + d * (-1343478805267877076848 + d * (390810726197471577936 + d *
    (-53011754267587623865 + d * (3042743604313803663 + d * (136277164007450811 + d *
    (-30974931343749527 + d * (1047429553635110 + d * (13088492338643 + d * (11948628310305 + d
    * (-539381670003 + d * (-171859262001))))))))))) + d ^ 12 * (5117460841 + d * (1235184212 +
    d * (58452364 + d * (2049658 + d * (62247 + d * (536 + d * (-1))))))))))))))))

private theorem selection_high_level_at_33 (d : ℚ) :
    orderSevenSelectionPolynomial d 33 = selectionExpandedAt33 d := by
  have hA : pointTateParameterUnivariateNumerator (orderSevenQuotient d) 33 =
      selectionNumeratorAt33 d := by
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
      selectionNumeratorAt33
    ring
  have hB : pointTateParameterUnivariateDenominator (orderSevenQuotient d) 33 =
      selectionDenominatorAt33 d := by
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
      selectionDenominatorAt33
    ring
  simp only [orderSevenSelectionPolynomial]
  rw [hA, hB]
  unfold orderSevenParameterHauptmodulNumerator orderSevenParameterCubic
    selectionNumeratorAt33 selectionDenominatorAt33 selectionExpandedAt33
  ring

private theorem selection_cofactor_eval_at_33 (d : ℚ) :
    (selectionCofactor d).eval 33 = selectionCofactorAt33 d := by
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
    selectionCofactorAt33
  simp
  ring

private theorem selection_factor_at_33 (d : ℚ) :
    selectionExpandedAt33 d =
      64 ^ 3 * orderSevenDualKernelPolynomial d 33 *
        selectionCofactorAt33 d := by
  unfold selectionExpandedAt33 orderSevenDualKernelPolynomial selectionCofactorAt33
  ring

theorem selectionEvalAt33 (d : ℚ) :
    Internal.SelectionEvalCertificate d 33 := by
  unfold Internal.SelectionEvalCertificate
  rw [selection_high_level_at_33, selection_cofactor_eval_at_33,
    selection_factor_at_33]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end

theorem solution (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 33 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt33 d
#print axioms solution
