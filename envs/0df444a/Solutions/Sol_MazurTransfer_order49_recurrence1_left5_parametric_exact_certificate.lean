-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_left5_parametric_exact_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T07:56:54.171029+00:00
-- url     : https://prove2.me/submissions/00ba55e1-5411-4e13-93da-da86a12e9c77

import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner5ExactHelperData
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace H5
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private def recurrence1Left5Row0Band0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 0 * (
    (2570652) * X ^ 1 +
    (2263599072) * X ^ 2 +
    (-5065786072536) * X ^ 3 +
    (-2102121447664056) * X ^ 4 +
    (3232646234998036024) * X ^ 5 +
    (-347692755598661926236) * X ^ 6 +
    (-63615199841770317661228) * X ^ 7 +
    (6488391289793667384180456) * X ^ 8
  )

private def recurrence1Left5Row0Band1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 9 * (
    (515770112541250400739280347) +
    (-34471909188876798927140148464) * X ^ 1 +
    (-2005469779909211657780678101778) * X ^ 2 +
    (62967733627978313592519761397922) * X ^ 3 +
    (4488193210880650443169755581049093) * X ^ 4 +
    (-27618688650865161959842114680516421) * X ^ 5 +
    (-5279607819616982017731518314418758267) * X ^ 6 +
    (-46929929105413013871333840603262576136) * X ^ 7 +
    (3161351902685020584513602965822214606836) * X ^ 8
  )

private def recurrence1Left5Row0Band2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 18 * (
    (67513655080740858007976670073465683016312) +
    (-761835665158715907843076968934986133032058) * X ^ 1 +
    (-37308226088320129195592970434384042879850930) * X ^ 2 +
    (-117597693876721682409237299461876452840896624) * X ^ 3 +
    (10561252127716693939716000241597508333480178784) * X ^ 4 +
    (130577503201465683285915236422170308832557712818) * X ^ 5 +
    (-1429933704138372777547217099991706150534287621630) * X ^ 6 +
    (-39357257774446710855437605567107803038523681577866) * X ^ 7 +
    (-21305106228622370687461199535961349607069830952818) * X ^ 8
  )

private def recurrence1Left5Row0Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 27 * (
    (6565795302972316736344597220853116219113940984092234) +
    (45450877916157395308146104095980594980068769454260438) * X ^ 1 +
    (-644378349033596595880188546129679839889916229048182321) * X ^ 2 +
    (-9273455527890662817344397162138706456542938133590557070) * X ^ 3 +
    (27141076398549066562224058308027637132354254705554455475) * X ^ 4 +
    (1110813229026295874604634595444166812282674245798400628062) * X ^ 5 +
    (2135240064828595568999183450837153163593609372989328531141) * X ^ 6 +
    (-91185775440001636347485533690706550775949828240913009819757) * X ^ 7 +
    (-511761947654496659489615293095327897094658752945067606260866) * X ^ 8
  )

private def recurrence1Left5Row0Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 36 * (
    (5338770898371938294611601437150788862809449691207559458426823) +
    (53082630815936273169563301176580378800702242900317328887836173) * X ^ 1 +
    (-209410025302708091861929526508954334081721069731553247839556256) * X ^ 2 +
    (-3865619096089072422720729604099075004090614765689919846312340825) * X ^ 3 +
    (3417482457188476868550625902249379215845117549614795298361609294) * X ^ 4 +
    (220570341755465343339398127215647853190432236890198706075110137587) * X ^ 5 +
    (234973317830168840240257161830012928722682346104846233446182907864) * X ^ 6 +
    (-10415542470681341496280466335678509434229728337924243118643159107353) * X ^ 7 +
    (-26261701404173589086545774107783486164023860509330355573771083274107) * X ^ 8
  )

private def recurrence1Left5Row0Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 45 * (
    (421401402449409497231963550459806341061698948296070576148741878853783) +
    (1562973587945276379321433100143041452153013894033416644578131686183297) * X ^ 1 +
    (-15039363118567384684862721884410416435524820997551931049839655017873937) * X ^ 2 +
    (-70471286683446241541641699663161322581993400872061738084528428500164860) * X ^ 3 +
    (486109633330860876570049279094384195261061678888310327427073926298292629) * X ^ 4 +
    (2631675080617611866450051873040948885907873375088044372932085228039356449) * X ^ 5 +
    (-14584353804900509340521429556319324780940982106284759066883470064860937525) * X ^ 6 +
    (-84476210084619736088460069632757031329496657541158967152644399491817877486) * X ^ 7 +
    (414247394119730285629693099705761016213227918553395919347659788464486110139) * X ^ 8
  )

private def recurrence1Left5Row0Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 54 * (
    (2370912236424323520199007205950716787009785177192544237779740828707216975256) +
    (-11257529405972950691485659974716069521643547506525441135291989359717774805487) * X ^ 1 +
    (-58452379628164216887915923224094789949395755604581887456374180148151189883282) * X ^ 2 +
    ((2 * 10 ^ 77 +
      92360655923539143761277715564577929016525532846160833496238768608764479973915)) * X ^ 3 +
    ((12 * 10 ^ 77 +
      57077977670441961051108875492650537858911898889384530056825422827872252670275)) * X ^ 4 +
    -((71 * 10 ^ 77 +
      74788976823328545869595749205445909630206567840354972017869439034165132953819)) * X ^ 5 +
    -((230 * 10 ^ 77 +
      23740213330382629887695256340788292024105924993774121803662184468254273310291)) * X ^ 6 +
    ((1636 * 10 ^ 77 +
      02521600831729684429512946685877922144963055714261683313879342951548408280143)) * X ^ 7 +
    ((3372 * 10 ^ 77 +
      17744546028612304754803972589549663499185375674447568809027879984638870947082)) * X ^ 8
  )

private def recurrence1Left5Row0Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 63 * (
    -((34010 * 10 ^ 77 +
      76988471850294603395119745553017049836943934646112112029170896978423241549345)) +
    -((31626 * 10 ^ 77 +
      38864600021850257127343708528030961629393505640254071615496679479363941328033)) * X ^ 1 +
    ((631453 * 10 ^ 77 +
      15793689001899289554913723052448381363607234561976849311865395703860043509416)) * X ^ 2 +
    -((115347 * 10 ^ 77 +
      87375901945172972677861904050107196555693125107494236873249293391854555362636)) * X ^ 3 +
    -((10208117 * 10 ^ 77 +
      18696876935549165004523635355111356739834765537164946317771629902328337761050)) * X ^ 4 +
    ((13722922 * 10 ^ 77 +
      11506663378246568344322102194036329674164257178160331653639653368038839043610)) * X ^ 5 +
    ((138128349 * 10 ^ 77 +
      22765481131300430397288171382131939152782844284223013401305014349922941825475)) * X ^ 6 +
    -((378720808 * 10 ^ 77 +
      88641190460351800993648796642994645560283815505524189327804865132308081943567)) * X ^ 7 +
    -((1437979093 * 10 ^ 77 +
      15411470841538813041020112929595454991983838893298069650832191909793443846562)) * X ^ 8
  )

private def recurrence1Left5Row0Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 72 * (
    ((7163810963 * 10 ^ 77 +
      32588342489848215526090731737466937064530318109442316537825033446037900912312)) +
    ((8428794617 * 10 ^ 77 +
      60646885358281032434061649773631571110585190739201477566148059345270935597085)) * X ^ 1 +
    -((103275790063 * 10 ^ 77 +
      85010233479065673628882974440782308884239631935498933401458747683846074127006)) * X ^ 2 +
    ((57855132812 * 10 ^ 77 +
      36055946234040611540197471739288696070752745336415601091721690033859627180891)) * X ^ 3 +
    ((1122642824621 * 10 ^ 77 +
      15815830746592305321313801508695708471636778284163752145501628202262695224159)) * X ^ 4 +
    -((2508339023488 * 10 ^ 77 +
      07894140357852168099196191129837828628063747407393776913453155657305917401209)) * X ^ 5 +
    -((8056327908835 * 10 ^ 77 +
      32480967618952116250065434111153506735276459410223628378186572086110286357887)) * X ^ 6 +
    ((40512702555894 * 10 ^ 77 +
      75375077083119145839304170453944680835159503759722696087828427439538450235281)) * X ^ 7 +
    ((10287159355231 * 10 ^ 77 +
      39634635457782700883078808244769161340281768859287404874010434552918841659860)) * X ^ 8
  )

private def recurrence1Left5Row0Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 81 * (
    -((417879873709293 * 10 ^ 77 +
      07591443570049302038461389450536389821623458513863158893808469756037892068837)) +
    ((676436749893859 * 10 ^ 77 +
      91512748289393486046102137409409766968670541797769665927585790811061633196407)) * X ^ 1 +
    ((2558520549486151 * 10 ^ 77 +
      28621095370435955137933835200643286794189614269158360208774792909861170375740)) * X ^ 2 +
    -((10914636452792145 * 10 ^ 77 +
      79711964682543863459586845348165416219779480038794690986226016235953709428262)) * X ^ 3 +
    -((524059064632243 * 10 ^ 77 +
      33079786813851374026277313340111019278259416088905042413368030662729452839067)) * X ^ 4 +
    ((91107084613503416 * 10 ^ 77 +
      87744984138806914389861143867875123241826397517672306637320179915530216679648)) * X ^ 5 +
    -((179702963767107877 * 10 ^ 77 +
      06201578525794802076481622371398825620797749908188750907179473792563977715407)) * X ^ 6 +
    -((331935437712006585 * 10 ^ 77 +
      07185802964530935126320097654300914028156001866503955186496070821460149882235)) * X ^ 7 +
    ((2019839092398334987 * 10 ^ 77 +
      95458909234223997079486167133362724393318599824111698897024266671998075340293)) * X ^ 8
  )

private def recurrence1Left5Row0Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 90 * (
    -((1870787146614827157 * 10 ^ 77 +
      43947052206600372530480836186538470595850198248392530308475717041578042589491)) +
    -((9935704254926296044 * 10 ^ 77 +
      65313426398423165049364032718373314878304301364619394996448785117640639209877)) * X ^ 1 +
    ((33756639743060321043 * 10 ^ 77 +
      50116010339879349604125968197008558755209566275950868588458910376400839676922)) * X ^ 2 +
    -((9699119577122518208 * 10 ^ 77 +
      79897080771174183012215318936653215078997516419599369193486859507676832598957)) * X ^ 3 +
    -((186635831914652465373 * 10 ^ 77 +
      47171561977907145791136203045706013885106523099256080776981799293827745046281)) * X ^ 4 +
    ((469634236083574733015 * 10 ^ 77 +
      00841650517959279854663597160094319020002283459707705802403456221908873017523)) * X ^ 5 +
    ((19275087456210039270 * 10 ^ 77 +
      22199448469685261099292898588079666182727616588680288569031983635479220295304)) * X ^ 6 +
    -((2618682478937944081951 * 10 ^ 77 +
      04904874889538622786830691526191625895414123562788753052766673983581991240429)) * X ^ 7 +
    ((5803418833981729897652 * 10 ^ 77 +
      00118020389754489386495627012963295967890036504000935158149885961859848856276)) * X ^ 8
  )

private def recurrence1Left5Row0Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 99 * (
    ((95444405785180516194 * 10 ^ 77 +
      22845022176138395395635258090427938477725074632485971047064092123767287132690)) +
    -((28400778201743267017273 * 10 ^ 77 +
      14859367883431868774958818403985969053004513816089197438936028441362532223866)) * X ^ 1 +
    ((64487640784398555837122 * 10 ^ 77 +
      57768630040946315733813087370682352850914427287136161268744901752506682258861)) * X ^ 2 +
    -((21205852692372417729430 * 10 ^ 77 +
      35418265242501651522840712503910990820780367221816581519970214475675861344535)) * X ^ 3 +
    -((226447069018075442802184 * 10 ^ 77 +
      36496194268781056170726869891795702752924592213747989257461319513634943464351)) * X ^ 4 +
    ((607197052314664445519326 * 10 ^ 77 +
      93855705549836725232079748083597815148829034585910175492847357970617063220674)) * X ^ 5 +
    -((514877667812268402695693 * 10 ^ 77 +
      68892745885001307961200634883581770185400526556358885756470508124897429822002)) * X ^ 6 +
    -((1069377099194773749759621 * 10 ^ 77 +
      25772208582928972858791422199045607522941228542838959799226340854317156708262)) * X ^ 7 +
    ((4265586856593045438591216 * 10 ^ 77 +
      64372596005804725459193746935146050689425987331015981296621676595523621361122)) * X ^ 8
  )

private def recurrence1Left5Row0Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 108 * (
    -((6148437617497036635666623 * 10 ^ 77 +
      66229385182015201793128042004693612702707636901047281149270849904557465181146)) +
    ((409450228986158742583809 * 10 ^ 77 +
      21975276881386929441262530160824971085610930281117254916587494453796207826035)) * X ^ 1 +
    ((17520884307179877937693093 * 10 ^ 77 +
      32960831827027072162286481302844088703506939403634279628148467812764617989066)) * X ^ 2 +
    -((40230222215165828696513386 * 10 ^ 77 +
      57845462992643942008477506663148795151569254062414849403320721833800528517953)) * X ^ 3 +
    ((42091351979968849446343881 * 10 ^ 77 +
      00030775818620514575430496161489751279003491707035788163982270450316815776528)) * X ^ 4 +
    ((8752306705715662176297967 * 10 ^ 77 +
      29755337744096622614926664629387993874749961568217650807978160903114690255489)) * X ^ 5 +
    -((116526505828623786210619481 * 10 ^ 77 +
      30708871800366004614719920983765564652964329372917116226433635762439395317195)) * X ^ 6 +
    ((224522956796529089753204787 * 10 ^ 77 +
      06252226364743983007733224973626364306090984572716152792420574526617651841519)) * X ^ 7 +
    -((223645783175382209431631178 * 10 ^ 77 +
      55030071077906672801521052604626970245629728833269530159462499562593215113351)) * X ^ 8
  )

private def recurrence1Left5Row0Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 117 * (
    ((24937756911554389165667518 * 10 ^ 77 +
      01747177725267402678185160859668476041353629662736202527203915089212860060544)) +
    ((340869077508771411954281996 * 10 ^ 77 +
      15670941977515952740789133805866558090331177923367945363383218785716911914368)) * X ^ 1 +
    -((684871381652695898338550703 * 10 ^ 77 +
      54058447062637113121419466589969117938057424439868459582594556620814115713156)) * X ^ 2 +
    ((749916966124010300044027610 * 10 ^ 77 +
      83228367647600090227427235258377417720661247485169950714679971294857486794131)) * X ^ 3 +
    -((394866366010966099759123055 * 10 ^ 77 +
      54789692617089500642964541636270142247454793704311537304409130025376574366004)) * X ^ 4 +
    -((263337885399706549081701071 * 10 ^ 77 +
      20502170866308474465797410578250566634644853441804321802238018315023918507107)) * X ^ 5 +
    ((883291184922530949509171400 * 10 ^ 77 +
      48737043022246383936260616832094169131397397192447198198028655366359336700330)) * X ^ 6 +
    -((1111205070069449309725700825 * 10 ^ 77 +
      23037530345278379185807658921313478002537354080017865091857635263345647669425)) * X ^ 7 +
    ((820585717479019625178415791 * 10 ^ 77 +
      66318507716698174675608381777248002288177281038174723956349692010218158779326)) * X ^ 8
  )

private def recurrence1Left5Row0Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 126 * (
    -((194587271760392677702746951 * 10 ^ 77 +
      79005759552552863673822506632841105007332460734889217447873053088487809283912)) +
    -((409552796805750593998508352 * 10 ^ 77 +
      07560345856379253811354405159903618800050908665119744471460463737006892633581)) * X ^ 1 +
    ((701043374241651518321469027 * 10 ^ 77 +
      65343802876894012622809186966711725981964098271512116414009307888467999660122)) * X ^ 2 +
    -((617922756534489126603237898 * 10 ^ 77 +
      29363311028315503770357564791145695082571855625882777938197043938410911241307)) * X ^ 3 +
    ((311705570982059626478007694 * 10 ^ 77 +
      05380837199291976592024686793391175108629394377643197583223896722365476359885)) * X ^ 4 +
    -((2387181405068752865718181 * 10 ^ 77 +
      31826127066711111713921807599596061756981838229075985289881252371329814803723)) * X ^ 5 +
    -((166877854027364559488831713 * 10 ^ 77 +
      73787059144747379373493501428825347260826968673922765779818554681659269969429)) * X ^ 6 +
    ((180961611603821323092433897 * 10 ^ 77 +
      75980273717111859459812160563817043316516543209709181208441193719134081203735)) * X ^ 7 +
    -((109186281689465736299105741 * 10 ^ 77 +
      35032463706907925686476845179523728547257655992839926620335531285130070650618)) * X ^ 8
  )

private def recurrence1Left5Row0Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 135 * (
    ((30293897730313515382249533 * 10 ^ 77 +
      05423655582171311591614251183160795717310176380796514069224748619216251994708)) +
    ((14436339947913471533763695 * 10 ^ 77 +
      96898147484879270465599096471911035980588864489034872265754289992867349559791)) * X ^ 1 +
    -((23919525982847844096873749 * 10 ^ 77 +
      69612126262354203318807865566213634893596066790072872530565870325956874767395)) * X ^ 2 +
    ((15654124125534424147899489 * 10 ^ 77 +
      13241534730222785289985332481847855359487059913006180630098851946241445373406)) * X ^ 3 +
    -((5430245612332205896086997 * 10 ^ 77 +
      59271056165241318542060112611620437219209112132407880969646305032010427855531)) * X ^ 4 +
    -((191685303650767900278196 * 10 ^ 77 +
      45054752926098527209572424858103926875725912652771708642566245546632729192819)) * X ^ 5 +
    ((1538266419122207549875123 * 10 ^ 77 +
      59716658871078987616107645459103256651341481486144265757934107601977383635111)) * X ^ 6 +
    -((1024446591285514537609025 * 10 ^ 77 +
      37408272983443076029033652424971620596688695644261334016519274544166048240536)) * X ^ 7 +
    ((340938370510198419503586 * 10 ^ 77 +
      19323833714718711954231787264275587638271754599087138366473334968410827946887)) * X ^ 8
  )

private def recurrence1Left5Row0Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 144 * (
    -((8277530749882515281769 * 10 ^ 77 +
      66452367298975816830924551782163341372840232725636876480758694726154707789584)) +
    -((57596332018790895140400 * 10 ^ 77 +
      56194042456144752006377466437906549943175400980898268851478586661955673316958)) * X ^ 1 +
    ((33507142903888618155234 * 10 ^ 77 +
      33126934123856126785121314578717852140437537520724221587291530772063718990472)) * X ^ 2 +
    -((8750707161936763901056 * 10 ^ 77 +
      72737205293572694712969221594498217409233310926548526025088630510890986621355)) * X ^ 3 +
    -((387196518634236998142 * 10 ^ 77 +
      29057100140294104808153145906148813456126052392613988265865024579481750209161)) * X ^ 4 +
    ((1303183369978016639945 * 10 ^ 77 +
      32908323701985837517561105269982392257965792556567455585592778204963165028890)) * X ^ 5 +
    -((519769199677179683799 * 10 ^ 77 +
      13241809261706878935642484036502150710575672492748621159786708798143843842620)) * X ^ 6 +
    ((71045365807857905659 * 10 ^ 77 +
      65084174064605566236096228038768234992499193317597826169660218708265077291133)) * X ^ 7 +
    ((23912546809704409632 * 10 ^ 77 +
      59825581447626939089154047324053628826393173787873036993271880424101996636726)) * X ^ 8
  )

private def recurrence1Left5Row0Band17 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 153 * (
    -((14691248983720173271 * 10 ^ 77 +
      24585444362295771248044065430012922137744261627259199754644394556363584504570)) +
    ((2832946080298061530 * 10 ^ 77 +
      21248952837924939449145841326574404728474033469732356516032441307904898642239)) * X ^ 1 +
    ((229913732520986748 * 10 ^ 77 +
      40416936708863524325701403160624056191794708453456008007062691763765386593555)) * X ^ 2 +
    -((250904138845157555 * 10 ^ 77 +
      80426918015417055350698366699917208751959826091873219729653461680981352055097)) * X ^ 3 +
    ((48816132033510630 * 10 ^ 77 +
      24526073285637197885157545654259992738368540682011797995283697879338666992195)) * X ^ 4 +
    ((2563478887115712 * 10 ^ 77 +
      38766841577808707018568555456786806301401737803247046530432840543895255784395)) * X ^ 5 +
    -((2905659100615262 * 10 ^ 77 +
      50237458166011670549448014567789154116585799304264470581806876943641147664661)) * X ^ 6 +
    ((413393823670811 * 10 ^ 77 +
      27223607879062538832427513972860860827377521750912682368909187779371983413257)) * X ^ 7 +
    ((48612258948116 * 10 ^ 77 +
      86781689001457451006018309665164323279766379860986685790308071929442544434174)) * X ^ 8
  )

private def recurrence1Left5Row0Band18 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 162 * (
    -((21299937889535 * 10 ^ 77 +
      82884479854778119218721401938154974031925423683008268778626001738825216362823)) +
    ((978441407417 * 10 ^ 77 +
      92167666566768371797854320698176583461654456307710271560274045745924877725924)) * X ^ 1 +
    ((500937583658 * 10 ^ 77 +
      06391105601000751429519633541704182262157286883728203949100690880347164984753)) * X ^ 2 +
    -((63558876516 * 10 ^ 77 +
      00904913764896593387246442665156951617123514300825842622933415378082367979878)) * X ^ 3 +
    -((7229605459 * 10 ^ 77 +
      73632764818837565180634855117219144602193721064893594404031875897042516379300)) * X ^ 4 +
    ((1525698114 * 10 ^ 77 +
      39137965110160348603348675667320896985362361672308995806921279275463989405754)) * X ^ 5 +
    ((87710101 * 10 ^ 77 +
      23319389612831223355850335535876379222906696456963081868268825652308984066078)) * X ^ 6 +
    -((23090304 * 10 ^ 77 +
      21833217145299688903991064047451214754421151382619155719325135524717282465114)) * X ^ 7 +
    -((1399377 * 10 ^ 77 +
      04825236363356650356226238285738117672006756776430611097879250437678904616069)) * X ^ 8
  )

private def recurrence1Left5Row0Band19 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 171 * (
    ((217505 * 10 ^ 77 +
      65530984537055837063758936379794920586617845746028425917509755241746025784336)) +
    ((23082 * 10 ^ 77 +
      29231566622509422366451378053773965980964476445406181415245534649460703972036)) * X ^ 1 +
    -((383 * 10 ^ 77 +
      88680354409501951172533181771187254984602739783699483851790910649362005092921)) * X ^ 2 +
    -((188 * 10 ^ 77 +
      99398178249304977682214499991369870612111381328024349125736372547617397579457)) * X ^ 3 +
    -((14 * 10 ^ 77 +
      92843838222526050427493640285871064791388631046931961163929220823957546679639)) * X ^ 4 +
    (-65678750716005577916644864083405203568184878739242387676075403385902314856025) * X ^ 5 +
    (-1883395951595518022557344200976976139093459770378490953152477863239791779543) * X ^ 6 +
    (-37103877689607318305412176997229659300397637720244101768566472446888346592) * X ^ 7 +
    (-511403728284353160214655582650899580339058492178954308249617913997403760) * X ^ 8
  )

private def recurrence1Left5Row0Band20 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 180 * (
    (-4924843346254478489454659039085114083693886935070657530674719074032281) +
    (-32444470461194971575494880343442653729621477050398624582740278037129) * X ^ 1 +
    (-138033053007303275411504539839398236657116890698048272441684739820) * X ^ 2 +
    (-316482592788380722967268216581259475294891960571809092417452588) * X ^ 3 +
    (-9825851324041471681786210112879903414163386304973582670959) * X ^ 4 +
    (2072251076063792190395290407266427852963222637937188281916) * X ^ 5 +
    (5030627611947435286219778090880810498409183938298745674) * X ^ 6 +
    (2472639724870934046836031067021349781871120070205156) * X ^ 7 +
    (-8127640852117529442014165019530426539310487479171) * X ^ 8
  )

private def recurrence1Left5Row0Band21 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  X ^ 189 * (
    (-14617164575359867753789076283618145240173553203) +
    (-9334475094053599304976846439515397378252581) * X ^ 1 +
    (-2527164199983884194886646723172401543701) * X ^ 2 +
    (-252232019767386271084028761598604371) * X ^ 3 +
    (-8863189096223638687390259815778) * X ^ 4 +
    (-50974886987732506556728327) * X ^ 5 +
    (-80547191109371686938) * X ^ 6 +
    (-255614117759) * X ^ 7 +
    (-203) * X ^ 8
  )

private def recurrence1Left5Row0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band0 +
  recurrence1Left5Row0Band1 +
  recurrence1Left5Row0Band2 +
  recurrence1Left5Row0Band3 +
  recurrence1Left5Row0Band4 +
  recurrence1Left5Row0Band5 +
  recurrence1Left5Row0Band6 +
  recurrence1Left5Row0Band7 +
  recurrence1Left5Row0Band8 +
  recurrence1Left5Row0Band9 +
  recurrence1Left5Row0Band10 +
  recurrence1Left5Row0Band11 +
  recurrence1Left5Row0Band12 +
  recurrence1Left5Row0Band13 +
  recurrence1Left5Row0Band14 +
  recurrence1Left5Row0Band15 +
  recurrence1Left5Row0Band16 +
  recurrence1Left5Row0Band17 +
  recurrence1Left5Row0Band18 +
  recurrence1Left5Row0Band19 +
  recurrence1Left5Row0Band20 +
  recurrence1Left5Row0Band21

private theorem recurrence1Left5Row0_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source5Block0 * MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square =
      recurrence1Left5Row0 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source5Block0 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock0
  unfold MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock1 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock2 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock3
  unfold MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock4 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock5 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock6
  unfold MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock7 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock8 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock9
  unfold MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock10 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock11 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock12
  unfold MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock13 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock14 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock15
  unfold MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock16 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock17 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock18
  unfold MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock19 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock20 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6SquareBlock21
  unfold recurrence1Left5Row0 recurrence1Left5Row0Band0 recurrence1Left5Row0Band1
  unfold recurrence1Left5Row0Band2 recurrence1Left5Row0Band3 recurrence1Left5Row0Band4
  unfold recurrence1Left5Row0Band5 recurrence1Left5Row0Band6 recurrence1Left5Row0Band7
  unfold recurrence1Left5Row0Band8 recurrence1Left5Row0Band9 recurrence1Left5Row0Band10
  unfold recurrence1Left5Row0Band11 recurrence1Left5Row0Band12 recurrence1Left5Row0Band13
  unfold recurrence1Left5Row0Band14 recurrence1Left5Row0Band15 recurrence1Left5Row0Band16
  unfold recurrence1Left5Row0Band17 recurrence1Left5Row0Band18 recurrence1Left5Row0Band19
  unfold recurrence1Left5Row0Band20 recurrence1Left5Row0Band21
  ring

private def recurrence1Left5Band0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band0

private theorem recurrence1Left5Band0_eq :
    recurrence1Left5Band0 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block0 := by
  unfold recurrence1Left5Band0 recurrence1Left5Row0Band0 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block0
  ring

private def recurrence1Left5Band1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band1

private theorem recurrence1Left5Band1_eq :
    recurrence1Left5Band1 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block1 := by
  unfold recurrence1Left5Band1 recurrence1Left5Row0Band1 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block1
  ring

private def recurrence1Left5Band2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band2

private theorem recurrence1Left5Band2_eq :
    recurrence1Left5Band2 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block2 := by
  unfold recurrence1Left5Band2 recurrence1Left5Row0Band2 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block2
  ring

private def recurrence1Left5Band3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band3

private theorem recurrence1Left5Band3_eq :
    recurrence1Left5Band3 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block3 := by
  unfold recurrence1Left5Band3 recurrence1Left5Row0Band3 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block3
  ring

private def recurrence1Left5Band4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band4

private theorem recurrence1Left5Band4_eq :
    recurrence1Left5Band4 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block4 := by
  unfold recurrence1Left5Band4 recurrence1Left5Row0Band4 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block4
  ring

private def recurrence1Left5Band5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band5

private theorem recurrence1Left5Band5_eq :
    recurrence1Left5Band5 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block5 := by
  unfold recurrence1Left5Band5 recurrence1Left5Row0Band5 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block5
  ring

private def recurrence1Left5Band6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band6

private theorem recurrence1Left5Band6_eq :
    recurrence1Left5Band6 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block6 := by
  unfold recurrence1Left5Band6 recurrence1Left5Row0Band6 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block6
  ring

private def recurrence1Left5Band7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band7

private theorem recurrence1Left5Band7_eq :
    recurrence1Left5Band7 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block7 := by
  unfold recurrence1Left5Band7 recurrence1Left5Row0Band7 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block7
  ring

private def recurrence1Left5Band8 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band8

private theorem recurrence1Left5Band8_eq :
    recurrence1Left5Band8 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block8 := by
  unfold recurrence1Left5Band8 recurrence1Left5Row0Band8 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block8
  ring

private def recurrence1Left5Band9 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band9

private theorem recurrence1Left5Band9_eq :
    recurrence1Left5Band9 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block9 := by
  unfold recurrence1Left5Band9 recurrence1Left5Row0Band9 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block9
  ring

private def recurrence1Left5Band10 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band10

private theorem recurrence1Left5Band10_eq :
    recurrence1Left5Band10 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block10 := by
  unfold recurrence1Left5Band10 recurrence1Left5Row0Band10 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block10
  ring

private def recurrence1Left5Band11 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band11

private theorem recurrence1Left5Band11_eq :
    recurrence1Left5Band11 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block11 := by
  unfold recurrence1Left5Band11 recurrence1Left5Row0Band11 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block11
  ring

private def recurrence1Left5Band12 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band12

private theorem recurrence1Left5Band12_eq :
    recurrence1Left5Band12 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block12 := by
  unfold recurrence1Left5Band12 recurrence1Left5Row0Band12 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block12
  ring

private def recurrence1Left5Band13 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band13

private theorem recurrence1Left5Band13_eq :
    recurrence1Left5Band13 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block13 := by
  unfold recurrence1Left5Band13 recurrence1Left5Row0Band13 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block13
  ring

private def recurrence1Left5Band14 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band14

private theorem recurrence1Left5Band14_eq :
    recurrence1Left5Band14 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block14 := by
  unfold recurrence1Left5Band14 recurrence1Left5Row0Band14 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block14
  ring

private def recurrence1Left5Band15 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band15

private theorem recurrence1Left5Band15_eq :
    recurrence1Left5Band15 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block15 := by
  unfold recurrence1Left5Band15 recurrence1Left5Row0Band15 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block15
  ring

private def recurrence1Left5Band16 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band16

private theorem recurrence1Left5Band16_eq :
    recurrence1Left5Band16 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block16 := by
  unfold recurrence1Left5Band16 recurrence1Left5Row0Band16 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block16
  ring

private def recurrence1Left5Band17 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band17

private theorem recurrence1Left5Band17_eq :
    recurrence1Left5Band17 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block17 := by
  unfold recurrence1Left5Band17 recurrence1Left5Row0Band17 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block17
  ring

private def recurrence1Left5Band18 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band18

private theorem recurrence1Left5Band18_eq :
    recurrence1Left5Band18 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block18 := by
  unfold recurrence1Left5Band18 recurrence1Left5Row0Band18 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block18
  ring

private def recurrence1Left5Band19 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band19

private theorem recurrence1Left5Band19_eq :
    recurrence1Left5Band19 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block19 := by
  unfold recurrence1Left5Band19 recurrence1Left5Row0Band19 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block19
  ring

private def recurrence1Left5Band20 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band20

private theorem recurrence1Left5Band20_eq :
    recurrence1Left5Band20 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block20 := by
  unfold recurrence1Left5Band20 recurrence1Left5Row0Band20 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block20
  ring

private def recurrence1Left5Band21 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0Band21

private theorem recurrence1Left5Band21_eq :
    recurrence1Left5Band21 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block21 := by
  unfold recurrence1Left5Band21 recurrence1Left5Row0Band21 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5Block21
  ring

private def recurrence1Left5Rows : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Row0

private def recurrence1Left5Bands : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient :=
  recurrence1Left5Band0 +
  recurrence1Left5Band1 +
  recurrence1Left5Band2 +
  recurrence1Left5Band3 +
  recurrence1Left5Band4 +
  recurrence1Left5Band5 +
  recurrence1Left5Band6 +
  recurrence1Left5Band7 +
  recurrence1Left5Band8 +
  recurrence1Left5Band9 +
  recurrence1Left5Band10 +
  recurrence1Left5Band11 +
  recurrence1Left5Band12 +
  recurrence1Left5Band13 +
  recurrence1Left5Band14 +
  recurrence1Left5Band15 +
  recurrence1Left5Band16 +
  recurrence1Left5Band17 +
  recurrence1Left5Band18 +
  recurrence1Left5Band19 +
  recurrence1Left5Band20 +
  recurrence1Left5Band21

theorem recurrence1Left5_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source5 * MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square =
      MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5 := by
  have rows :
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source5 * MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square =
        recurrence1Left5Rows := by
    unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source5 recurrence1Left5Rows
    exact recurrence1Left5Row0_eq
  rw [rows]
  have rearrange : recurrence1Left5Rows = recurrence1Left5Bands := by
    unfold recurrence1Left5Rows recurrence1Left5Bands recurrence1Left5Row0 recurrence1Left5Band0
    unfold recurrence1Left5Band1 recurrence1Left5Band2 recurrence1Left5Band3 recurrence1Left5Band4
    unfold recurrence1Left5Band5 recurrence1Left5Band6 recurrence1Left5Band7 recurrence1Left5Band8
    unfold recurrence1Left5Band9 recurrence1Left5Band10 recurrence1Left5Band11
    unfold recurrence1Left5Band12 recurrence1Left5Band13 recurrence1Left5Band14
    unfold recurrence1Left5Band15 recurrence1Left5Band16 recurrence1Left5Band17
    unfold recurrence1Left5Band18 recurrence1Left5Band19 recurrence1Left5Band20
    unfold recurrence1Left5Band21
    ring
  rw [rearrange]
  unfold recurrence1Left5Bands MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5
  rw [recurrence1Left5Band0_eq]
  rw [recurrence1Left5Band1_eq]
  rw [recurrence1Left5Band2_eq]
  rw [recurrence1Left5Band3_eq]
  rw [recurrence1Left5Band4_eq]
  rw [recurrence1Left5Band5_eq]
  rw [recurrence1Left5Band6_eq]
  rw [recurrence1Left5Band7_eq]
  rw [recurrence1Left5Band8_eq]
  rw [recurrence1Left5Band9_eq]
  rw [recurrence1Left5Band10_eq]
  rw [recurrence1Left5Band11_eq]
  rw [recurrence1Left5Band12_eq]
  rw [recurrence1Left5Band13_eq]
  rw [recurrence1Left5Band14_eq]
  rw [recurrence1Left5Band15_eq]
  rw [recurrence1Left5Band16_eq]
  rw [recurrence1Left5Band17_eq]
  rw [recurrence1Left5Band18_eq]
  rw [recurrence1Left5Band19_eq]
  rw [recurrence1Left5Band20_eq]
  rw [recurrence1Left5Band21_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end H5

theorem solution : MazurTransfer.ExactEqualityCertificate
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source5 * MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square)
    (MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5) := by
  exact ⟨H5.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5_eq⟩
#print axioms solution
