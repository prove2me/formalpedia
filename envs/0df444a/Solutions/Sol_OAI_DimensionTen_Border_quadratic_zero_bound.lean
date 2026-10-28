-- Prove2me | solution 1 for OAI.DimensionTen.Border.quadratic_zero_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:45:00.930979+00:00
-- url     : https://prove2.me/submissions/a5bd8c5b-a84b-4b48-a024-3c68d3c49467

import Mathlib
import Definitions.Def_OAIQ033D009
import Definitions.Def_OAIQ033D014
import Theorems.Thm_OAI_DimensionTen_Mod139_iterate18
import Theorems.Thm_OAI_DimensionTen_exists_swap_of_mod131

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Model
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem initial {R : Type*} [CommRing R] (z : R) : z ^ (139 ^ 0) = u0 z := by simp [u0]

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_IntegerPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

lemma coef_131_0 : ((-665456935831295645613234276870960 : ℤ) : ZMod 131) = (66 : ZMod 131) := by decide +kernel
lemma coef_131_1 : ((-70575490389691608208970825963579579734790687104242531156794252400 : ℤ) : ZMod 131) = (59 : ZMod 131) := by decide +kernel
lemma coef_131_2 : ((145204575748123705650598860122042297964140180806502873813425954437770925496552439336297911807152000 : ℤ) : ZMod 131) = (49 : ZMod 131) := by decide +kernel
lemma coef_131_3 : ((-35324838830202393213114710617144206880545881202172927720865474148390980209388806187550300213113700416597412380444619467558313120000 : ℤ) : ZMod 131) = (86 : ZMod 131) := by decide +kernel
lemma coef_131_4 : ((373565650934774887461173450615958673493665750145833416276706195065625377037257320323651912502138867646885039242665453554378883071785987397285956044288246752000000 : ℤ) : ZMod 131) = (37 : ZMod 131) := by decide +kernel
lemma coef_131_5 : ((1221247532914883428738232812315046413061003261754365921877331401690772085408337009866167041104811173917721563989083295894997519285879820644602218589359930080044045784701600336896172318351552000000 : ℤ) : ZMod 131) = (7 : ZMod 131) := by decide +kernel
lemma coef_131_6 : ((-248227637152475705027939375857278526128191272750984168929977414072990649655673065160190565283923935144328649963473688624322944637031495498096318971767466342970191076754053510390097551205920734946099494349011595986009016320000000 : ℤ) : ZMod 131) = (77 : ZMod 131) := by decide +kernel
lemma coef_131_7 : ((23987898748033982540672860523700865395338187584784902027097207883389242545617842033943633110512117271742643190645306300993695952546671697315106563700443682653623151506540994176376096734479969113402657992738820843936302180323975678376815544328820255590400000000 : ℤ) : ZMod 131) = (85 : ZMod 131) := by decide +kernel
lemma coef_131_8 : ((-1171308828589766784667174319064418542798135133484982791854491081649943231360093785409472006445243262855246426572170988410104927443954726055604498601479060662278001768673622504306995915615815163705741569269783733808816002389524109550321410806269620903448193875229330238654480165635072000000000 : ℤ) : ZMod 131) = (116 : ZMod 131) := by decide +kernel
lemma coef_131_9 : ((9418076163852223744432430014364091808485209898268329041429484569331398431107415197968026807215347240401736075163106970860375437764441639386759444924342265991793540088391019157445548247844788073792441943995585891632831540649213169911827703330754567896340380609774093821467596292667988969060929685782740051333867520000000000 : ℤ) : ZMod 131) = (17 : ZMod 131) := by decide +kernel
lemma coef_131_10 : ((2379351982660918187351912781958188527717967481429203927909200858573699275008394894183277671168447409642612098439982572413522546000040986498273641717234153243897007250606150778122646421703817983494954617791128567739285620364189110954410697514797765886291714388494664729026689529953663266988303413000134427206176735476450561111234207094565608243200000000000 : ℤ) : ZMod 131) = (54 : ZMod 131) := by decide +kernel
lemma coef_131_11 : ((-156443788709025742196345911143201398522107585903943872656350511938867845971206431668038085111377071526334593976793592772236822162619007312610358668945562381934474011199900422427845078146852059081562149156225635557185181304351482728149253212060717470179340715966538846953566303581355673324261441159585174786519237690702352218433699357759363998509903389517501570746482257203200000000000000 : ℤ) : ZMod 131) = (100 : ZMod 131) := by decide +kernel
lemma coef_131_12 : ((4900890101564280273384249662632200864363178448207658026058163336136819615272493885470202054565224538142000936511937843307007141485106069287814351270516554069895222315717069012981831431598688971184588468042505208877149369556657292564526267236422804943134514567637453529579229073192380181445210152334600678520463948715012876905929334440543179125298895959992011293893481380162364702394538413670540082328535040000000000000 : ℤ) : ZMod 131) = (70 : ZMod 131) := by decide +kernel
lemma coef_131_13 : ((-84104307174298673686167552255023640494586429007832021068263654225131496108888450236021703884431876764525210998671836899723767574650679562923240549613170660460307111553062077806825303303373793065431974171250181275915638689447630046090976265566391394588988957333827128766847100966792731531401924178962941086742313997809833999852121787629675539133006863302099166667861554529199671567381395010640407518426305516067478326139731889369074892800000000000000 : ℤ) : ZMod 131) = (2 : ZMod 131) := by decide +kernel
lemma coef_131_14 : ((675860552142364300469163135239922215844669725914434221808961587832864654839688852714377465846874183474661558953416089505955745772157789761536300845401390976278172003633735629354916823207663419987549669250042714970662428618786997007804393564088687435177258735743667457380692013561927748177389045537156630683615468224776124736218311770991358194005151667711594323471452495210584512969519473278662518864183000362256079240789122668752515792267237678356626639740742926336000000000000000 : ℤ) : ZMod 131) = (114 : ZMod 131) := by decide +kernel
lemma coef_131_15 : ((464264497883407444747214497780812992686704524760753459744647662220415750416845824659077752493206710993356675945744931523943090697063536003409707838510945285234954377033375647019503467236967613563967236378430128420958879199174432425365805238966092079988382033895233428997733820972532862160052383779427027697929911022006616671493677356268258333730255560145075340313333181727787699892890692686951362386275741868725537594362933484314558383739147305382918898686952977786128912938230214944318784798720000000000000000 : ℤ) : ZMod 131) = (71 : ZMod 131) := by decide +kernel
lemma coef_131_16 : ((-46078962234330275978393081039900872188683319775920327128308452687890209275764118451319687474009314096598155961959548923384930131718444660825818480828257818821039017264033763526190311506189940321255132637170583750838824867220822705767283964636390962873055630047046796945200799791451986485780961563108553013724002067700649315332952049979688029591671182364417015107032858404981473456796680608866020804392285926068306658664953047502713815667799656452571900290324373867393260683805253816278147547319199730096639224635584878424883200000000000000000 : ℤ) : ZMod 131) = (23 : ZMod 131) := by decide +kernel
lemma coef_131_17 : ((229540072167944847226680415208013118338761677374944768373442556047077491167862762106359122660044266376402295481008188646997320599898453491372250113733518589454936121739510066262153803563671695844108844188342855909377211756360861260377168676543780626494372504766738464872238720120608406900323489717675021679247953712129677892949203666168430318973900550171283869938908653927859069485683785552618689290268121667910013497695005067467335610102307071987167020413797861407454637885276358908659560709050422061741810597789529542860159000644434640948505635320758272000000000000000000 : ℤ) : ZMod 131) = (64 : ZMod 131) := by decide +kernel
lemma coef_131_18 : ((50511259664407229159646828548337393831498164764442804655127386655612901648776121372469336914091639720740949450692522422501871756701072556552050895980619323103036951478408656634191362563383127130617057997298235140794077506240567579912973487530312823172729903267062062135892781938802036475675819137510666873059408131836941370912492276716379814401275115222108476610434649500821249715911952605938441183268983422802130006238945591464489363332367504221919288966190285721674362152675650209632960747379797873753029847424190752816297979945928310952397381467134670500671900306775579122183700480000000000000000000 : ℤ) : ZMod 131) = (47 : ZMod 131) := by decide +kernel
lemma coef_131_19 : ((-1424105438854051274637383580879187889947095521139556310680850766315834321551239556574203521562568408091279110770199392239672103401933480228396676040102864674581064663417300893715619893996546336746566239320115175015022647808252252957375990525415013961893949766339014426315700834891145618186295338735724851165176076792616990913196521711297962346422135606209029955414419424094778362387247876506714514958332570454743222106183632267250532813404938217795375126355778437850775218722352764943835257588425767268897713027152377493877523758390937382693586850604084390990278979077079727932490410447293788987687686157708243763200000000000000000000 : ℤ) : ZMod 131) = (50 : ZMod 131) := by decide +kernel

lemma F_reduction_131 : F.map (Int.castRingHom (ZMod 131)) = Mod131.f X := by
  rw [F_map]
  simp only [FP, ← C_eq_intCast, coef_131_0, coef_131_1, coef_131_2, coef_131_3, coef_131_4, coef_131_5, coef_131_6, coef_131_7, coef_131_8, coef_131_9, coef_131_10, coef_131_11, coef_131_12, coef_131_13, coef_131_14, coef_131_15, coef_131_16, coef_131_17, coef_131_18, coef_131_19,
    map_ofNat, Mod131.f, mul_one]

lemma coef_139_0 : ((-665456935831295645613234276870960 : ℤ) : ZMod 139) = (128 : ZMod 139) := by decide +kernel
lemma coef_139_1 : ((-70575490389691608208970825963579579734790687104242531156794252400 : ℤ) : ZMod 139) = (102 : ZMod 139) := by decide +kernel
lemma coef_139_2 : ((145204575748123705650598860122042297964140180806502873813425954437770925496552439336297911807152000 : ℤ) : ZMod 139) = (0 : ZMod 139) := by decide +kernel
lemma coef_139_3 : ((-35324838830202393213114710617144206880545881202172927720865474148390980209388806187550300213113700416597412380444619467558313120000 : ℤ) : ZMod 139) = (116 : ZMod 139) := by decide +kernel
lemma coef_139_4 : ((373565650934774887461173450615958673493665750145833416276706195065625377037257320323651912502138867646885039242665453554378883071785987397285956044288246752000000 : ℤ) : ZMod 139) = (89 : ZMod 139) := by decide +kernel
lemma coef_139_5 : ((1221247532914883428738232812315046413061003261754365921877331401690772085408337009866167041104811173917721563989083295894997519285879820644602218589359930080044045784701600336896172318351552000000 : ℤ) : ZMod 139) = (58 : ZMod 139) := by decide +kernel
lemma coef_139_6 : ((-248227637152475705027939375857278526128191272750984168929977414072990649655673065160190565283923935144328649963473688624322944637031495498096318971767466342970191076754053510390097551205920734946099494349011595986009016320000000 : ℤ) : ZMod 139) = (130 : ZMod 139) := by decide +kernel
lemma coef_139_7 : ((23987898748033982540672860523700865395338187584784902027097207883389242545617842033943633110512117271742643190645306300993695952546671697315106563700443682653623151506540994176376096734479969113402657992738820843936302180323975678376815544328820255590400000000 : ℤ) : ZMod 139) = (34 : ZMod 139) := by decide +kernel
lemma coef_139_8 : ((-1171308828589766784667174319064418542798135133484982791854491081649943231360093785409472006445243262855246426572170988410104927443954726055604498601479060662278001768673622504306995915615815163705741569269783733808816002389524109550321410806269620903448193875229330238654480165635072000000000 : ℤ) : ZMod 139) = (31 : ZMod 139) := by decide +kernel
lemma coef_139_9 : ((9418076163852223744432430014364091808485209898268329041429484569331398431107415197968026807215347240401736075163106970860375437764441639386759444924342265991793540088391019157445548247844788073792441943995585891632831540649213169911827703330754567896340380609774093821467596292667988969060929685782740051333867520000000000 : ℤ) : ZMod 139) = (136 : ZMod 139) := by decide +kernel
lemma coef_139_10 : ((2379351982660918187351912781958188527717967481429203927909200858573699275008394894183277671168447409642612098439982572413522546000040986498273641717234153243897007250606150778122646421703817983494954617791128567739285620364189110954410697514797765886291714388494664729026689529953663266988303413000134427206176735476450561111234207094565608243200000000000 : ℤ) : ZMod 139) = (119 : ZMod 139) := by decide +kernel
lemma coef_139_11 : ((-156443788709025742196345911143201398522107585903943872656350511938867845971206431668038085111377071526334593976793592772236822162619007312610358668945562381934474011199900422427845078146852059081562149156225635557185181304351482728149253212060717470179340715966538846953566303581355673324261441159585174786519237690702352218433699357759363998509903389517501570746482257203200000000000000 : ℤ) : ZMod 139) = (78 : ZMod 139) := by decide +kernel
lemma coef_139_12 : ((4900890101564280273384249662632200864363178448207658026058163336136819615272493885470202054565224538142000936511937843307007141485106069287814351270516554069895222315717069012981831431598688971184588468042505208877149369556657292564526267236422804943134514567637453529579229073192380181445210152334600678520463948715012876905929334440543179125298895959992011293893481380162364702394538413670540082328535040000000000000 : ℤ) : ZMod 139) = (77 : ZMod 139) := by decide +kernel
lemma coef_139_13 : ((-84104307174298673686167552255023640494586429007832021068263654225131496108888450236021703884431876764525210998671836899723767574650679562923240549613170660460307111553062077806825303303373793065431974171250181275915638689447630046090976265566391394588988957333827128766847100966792731531401924178962941086742313997809833999852121787629675539133006863302099166667861554529199671567381395010640407518426305516067478326139731889369074892800000000000000 : ℤ) : ZMod 139) = (48 : ZMod 139) := by decide +kernel
lemma coef_139_14 : ((675860552142364300469163135239922215844669725914434221808961587832864654839688852714377465846874183474661558953416089505955745772157789761536300845401390976278172003633735629354916823207663419987549669250042714970662428618786997007804393564088687435177258735743667457380692013561927748177389045537156630683615468224776124736218311770991358194005151667711594323471452495210584512969519473278662518864183000362256079240789122668752515792267237678356626639740742926336000000000000000 : ℤ) : ZMod 139) = (42 : ZMod 139) := by decide +kernel
lemma coef_139_15 : ((464264497883407444747214497780812992686704524760753459744647662220415750416845824659077752493206710993356675945744931523943090697063536003409707838510945285234954377033375647019503467236967613563967236378430128420958879199174432425365805238966092079988382033895233428997733820972532862160052383779427027697929911022006616671493677356268258333730255560145075340313333181727787699892890692686951362386275741868725537594362933484314558383739147305382918898686952977786128912938230214944318784798720000000000000000 : ℤ) : ZMod 139) = (109 : ZMod 139) := by decide +kernel
lemma coef_139_16 : ((-46078962234330275978393081039900872188683319775920327128308452687890209275764118451319687474009314096598155961959548923384930131718444660825818480828257818821039017264033763526190311506189940321255132637170583750838824867220822705767283964636390962873055630047046796945200799791451986485780961563108553013724002067700649315332952049979688029591671182364417015107032858404981473456796680608866020804392285926068306658664953047502713815667799656452571900290324373867393260683805253816278147547319199730096639224635584878424883200000000000000000 : ℤ) : ZMod 139) = (132 : ZMod 139) := by decide +kernel
lemma coef_139_17 : ((229540072167944847226680415208013118338761677374944768373442556047077491167862762106359122660044266376402295481008188646997320599898453491372250113733518589454936121739510066262153803563671695844108844188342855909377211756360861260377168676543780626494372504766738464872238720120608406900323489717675021679247953712129677892949203666168430318973900550171283869938908653927859069485683785552618689290268121667910013497695005067467335610102307071987167020413797861407454637885276358908659560709050422061741810597789529542860159000644434640948505635320758272000000000000000000 : ℤ) : ZMod 139) = (125 : ZMod 139) := by decide +kernel
lemma coef_139_18 : ((50511259664407229159646828548337393831498164764442804655127386655612901648776121372469336914091639720740949450692522422501871756701072556552050895980619323103036951478408656634191362563383127130617057997298235140794077506240567579912973487530312823172729903267062062135892781938802036475675819137510666873059408131836941370912492276716379814401275115222108476610434649500821249715911952605938441183268983422802130006238945591464489363332367504221919288966190285721674362152675650209632960747379797873753029847424190752816297979945928310952397381467134670500671900306775579122183700480000000000000000000 : ℤ) : ZMod 139) = (122 : ZMod 139) := by decide +kernel
lemma coef_139_19 : ((-1424105438854051274637383580879187889947095521139556310680850766315834321551239556574203521562568408091279110770199392239672103401933480228396676040102864674581064663417300893715619893996546336746566239320115175015022647808252252957375990525415013961893949766339014426315700834891145618186295338735724851165176076792616990913196521711297962346422135606209029955414419424094778362387247876506714514958332570454743222106183632267250532813404938217795375126355778437850775218722352764943835257588425767268897713027152377493877523758390937382693586850604084390990278979077079727932490410447293788987687686157708243763200000000000000000000 : ℤ) : ZMod 139) = (105 : ZMod 139) := by decide +kernel

lemma F_reduction_139 : F.map (Int.castRingHom (ZMod 139)) = Mod139.f X := by
  rw [F_map]
  simp only [FP, ← C_eq_intCast, coef_139_0, coef_139_1, coef_139_2, coef_139_3, coef_139_4, coef_139_5, coef_139_6, coef_139_7, coef_139_8, coef_139_9, coef_139_10, coef_139_11, coef_139_12, coef_139_13, coef_139_14, coef_139_15, coef_139_16, coef_139_17, coef_139_18, coef_139_19,
    map_ofNat, Mod139.f, mul_one, zero_add, C_0]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_NormalizedMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma cast_mulVec (B : Matrix (Fin 20) (Fin 20) ℤ) (v : Fin 20 → ℤ) :
    (fun j => ((B *ᵥ v) j : ℚ)) = B.map (Int.castRingHom ℚ) *ᵥ (fun j => (v j : ℚ)) := by
  ext j
  exact (Int.castRingHom ℚ).map_mulVec B v j

lemma cast_single (i : Fin 20) :
    (fun j => ((Pi.single i 1 : Fin 20 → ℤ) j : ℚ)) = eQ i := by
  ext j
  simp [eQ, Pi.single_apply]

lemma normalize_shift (B : Matrix (Fin 20) (Fin 20) ℤ) (i j : Fin 20)
    (h : B *ᵥ Pi.single i 1 = d • Pi.single j 1) :
    ((d : ℚ)⁻¹ • B.map (Int.castRingHom ℚ)) *ᵥ eQ i = eQ j := by
  have hh := congrArg (fun v : Fin 20 → ℤ => fun k => (v k : ℚ)) h
  rw [cast_mulVec, cast_single] at hh
  have hcast : (fun k => ((d • (Pi.single j 1 : Fin 20 → ℤ)) k : ℚ)) = (d : ℚ) • eQ j := by
    ext k
    simp [eQ, Pi.single_apply, smul_eq_mul]
  rw [hcast] at hh
  rw [Matrix.smul_mulVec, hh, smul_smul, inv_mul_cancel₀ dQ_ne_zero, one_smul]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_BorderField
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsGaloisRatK _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma E_one : E 1 = eQ 0 := by change rho 1 *ᵥ eQ 0 = _; simp
lemma E_mul (a b : L) : E (a * b) = rho a *ᵥ E b := by
  change rho (a * b) *ᵥ eQ 0 = rho a *ᵥ (rho b *ᵥ eQ 0)
  rw [map_mul, Matrix.mulVec_mulVec]

lemma rho_alpha (i : Fin 3) : rho (alpha i) = NB i := by
  fin_cases i
  · change rho ((d : ℚ)⁻¹ • AdjoinRoot.root fQ) = _
    rw [map_smul, rho_root]
    rfl
  · exact (NB_in_image 1).choose_spec
  · exact (NB_in_image 2).choose_spec

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_LowBasis
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsGaloisRatK _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma low_zero {R : Type*} [CommRing R] (t : Fin 3 → R) : low t 0 = 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma low_shift_1 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 1 = t 2 * low t 0 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_1 : NB 2 *ᵥ eQ 0 = eQ 1 := by
  exact normalize_shift B2 0 1 shift_1

lemma low_shift_2 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 2 = t 1 * low t 0 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_2 : NB 1 *ᵥ eQ 0 = eQ 2 := by
  exact normalize_shift B1 0 2 shift_2

lemma low_shift_3 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 3 = t 0 * low t 0 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_3 : NB 0 *ᵥ eQ 0 = eQ 3 := by
  exact normalize_shift B0 0 3 shift_3

lemma low_shift_4 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 4 = t 2 * low t 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_4 : NB 2 *ᵥ eQ 1 = eQ 4 := by
  exact normalize_shift B2 1 4 shift_4

lemma low_shift_5 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 5 = t 1 * low t 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_5 : NB 1 *ᵥ eQ 1 = eQ 5 := by
  exact normalize_shift B1 1 5 shift_5

lemma low_shift_6 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 6 = t 1 * low t 2 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_6 : NB 1 *ᵥ eQ 2 = eQ 6 := by
  exact normalize_shift B1 2 6 shift_6

lemma low_shift_7 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 7 = t 0 * low t 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_7 : NB 0 *ᵥ eQ 1 = eQ 7 := by
  exact normalize_shift B0 1 7 shift_7

lemma low_shift_8 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 8 = t 0 * low t 2 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_8 : NB 0 *ᵥ eQ 2 = eQ 8 := by
  exact normalize_shift B0 2 8 shift_8

lemma low_shift_9 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 9 = t 0 * low t 3 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_9 : NB 0 *ᵥ eQ 3 = eQ 9 := by
  exact normalize_shift B0 3 9 shift_9

lemma low_shift_10 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 10 = t 2 * low t 4 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_10 : NB 2 *ᵥ eQ 4 = eQ 10 := by
  exact normalize_shift B2 4 10 shift_10

lemma low_shift_11 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 11 = t 1 * low t 4 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_11 : NB 1 *ᵥ eQ 4 = eQ 11 := by
  exact normalize_shift B1 4 11 shift_11

lemma low_shift_12 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 12 = t 1 * low t 5 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_12 : NB 1 *ᵥ eQ 5 = eQ 12 := by
  exact normalize_shift B1 5 12 shift_12

lemma low_shift_13 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 13 = t 1 * low t 6 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_13 : NB 1 *ᵥ eQ 6 = eQ 13 := by
  exact normalize_shift B1 6 13 shift_13

lemma low_shift_14 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 14 = t 0 * low t 4 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_14 : NB 0 *ᵥ eQ 4 = eQ 14 := by
  exact normalize_shift B0 4 14 shift_14

lemma low_shift_15 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 15 = t 0 * low t 5 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_15 : NB 0 *ᵥ eQ 5 = eQ 15 := by
  exact normalize_shift B0 5 15 shift_15

lemma low_shift_16 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 16 = t 0 * low t 6 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_16 : NB 0 *ᵥ eQ 6 = eQ 16 := by
  exact normalize_shift B0 6 16 shift_16

lemma low_shift_17 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 17 = t 0 * low t 7 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_17 : NB 0 *ᵥ eQ 7 = eQ 17 := by
  exact normalize_shift B0 7 17 shift_17

lemma low_shift_18 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 18 = t 0 * low t 8 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_18 : NB 0 *ᵥ eQ 8 = eQ 18 := by
  exact normalize_shift B0 8 18 shift_18

lemma low_shift_19 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 19 = t 0 * low t 9 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_19 : NB 0 *ᵥ eQ 9 = eQ 19 := by
  exact normalize_shift B0 9 19 shift_19

lemma E_low_0 : E (low alpha 0) = eQ 0 := by rw [low_zero, E_one]

lemma E_low_1 : E (low alpha 1) = eQ 1 := by
  rw [low_shift_1, E_mul, rho_alpha, E_low_0, NB_shift_1]

lemma E_low_2 : E (low alpha 2) = eQ 2 := by
  rw [low_shift_2, E_mul, rho_alpha, E_low_0, NB_shift_2]

lemma E_low_3 : E (low alpha 3) = eQ 3 := by
  rw [low_shift_3, E_mul, rho_alpha, E_low_0, NB_shift_3]

lemma E_low_4 : E (low alpha 4) = eQ 4 := by
  rw [low_shift_4, E_mul, rho_alpha, E_low_1, NB_shift_4]

lemma E_low_5 : E (low alpha 5) = eQ 5 := by
  rw [low_shift_5, E_mul, rho_alpha, E_low_1, NB_shift_5]

lemma E_low_6 : E (low alpha 6) = eQ 6 := by
  rw [low_shift_6, E_mul, rho_alpha, E_low_2, NB_shift_6]

lemma E_low_7 : E (low alpha 7) = eQ 7 := by
  rw [low_shift_7, E_mul, rho_alpha, E_low_1, NB_shift_7]

lemma E_low_8 : E (low alpha 8) = eQ 8 := by
  rw [low_shift_8, E_mul, rho_alpha, E_low_2, NB_shift_8]

lemma E_low_9 : E (low alpha 9) = eQ 9 := by
  rw [low_shift_9, E_mul, rho_alpha, E_low_3, NB_shift_9]

lemma E_low_10 : E (low alpha 10) = eQ 10 := by
  rw [low_shift_10, E_mul, rho_alpha, E_low_4, NB_shift_10]

lemma E_low_11 : E (low alpha 11) = eQ 11 := by
  rw [low_shift_11, E_mul, rho_alpha, E_low_4, NB_shift_11]

lemma E_low_12 : E (low alpha 12) = eQ 12 := by
  rw [low_shift_12, E_mul, rho_alpha, E_low_5, NB_shift_12]

lemma E_low_13 : E (low alpha 13) = eQ 13 := by
  rw [low_shift_13, E_mul, rho_alpha, E_low_6, NB_shift_13]

lemma E_low_14 : E (low alpha 14) = eQ 14 := by
  rw [low_shift_14, E_mul, rho_alpha, E_low_4, NB_shift_14]

lemma E_low_15 : E (low alpha 15) = eQ 15 := by
  rw [low_shift_15, E_mul, rho_alpha, E_low_5, NB_shift_15]

lemma E_low_16 : E (low alpha 16) = eQ 16 := by
  rw [low_shift_16, E_mul, rho_alpha, E_low_6, NB_shift_16]

lemma E_low_17 : E (low alpha 17) = eQ 17 := by
  rw [low_shift_17, E_mul, rho_alpha, E_low_7, NB_shift_17]

lemma E_low_18 : E (low alpha 18) = eQ 18 := by
  rw [low_shift_18, E_mul, rho_alpha, E_low_8, NB_shift_18]

lemma E_low_19 : E (low alpha 19) = eQ 19 := by
  rw [low_shift_19, E_mul, rho_alpha, E_low_9, NB_shift_19]

lemma E_low (i : Fin 20) : E (low alpha i) = eQ i := by
  fin_cases i
  · exact E_low_0
  · exact E_low_1
  · exact E_low_2
  · exact E_low_3
  · exact E_low_4
  · exact E_low_5
  · exact E_low_6
  · exact E_low_7
  · exact E_low_8
  · exact E_low_9
  · exact E_low_10
  · exact E_low_11
  · exact E_low_12
  · exact E_low_13
  · exact E_low_14
  · exact E_low_15
  · exact E_low_16
  · exact E_low_17
  · exact E_low_18
  · exact E_low_19


lemma basis_eq (i : Fin 20) : basis i = low alpha i := by
  apply E_injective
  simp only [basis, Module.Basis.map_apply, Pi.basisFun_apply, E_low, eQ]
  exact (LinearEquiv.ofBijective E ⟨E_injective, E_surjective⟩).apply_symm_apply _

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_AlphaMinors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma mon_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : Fin 3 → R) (i : Fin 35) : f (mon t i) = mon (fun j => f (t j)) i := by
  simp [mon]

lemma low_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : Fin 3 → R) (i : Fin 20) : f (low t i) = low (fun j => f (t j)) i := by
  exact mon_map f t _

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_RootReduction
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma map_eq_prod_rootInteger {K : Type*} [Field K] [CharZero K]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hsp : (f.map (algebraMap ℤ K)).Splits) :
    f.map (algebraMap ℤ (𝓞 K)) = ∏ x : f.rootSet K, (X - C (rootInteger f hm x)) := by
  classical
  apply Polynomial.map_injective _ (RingOfIntegers.coe_injective (K := K))
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ (𝓞 K) K]
  exact map_eq_prod_rootSet f hm hs hsp

lemma reduction_factorization {K k : Type*} [Field K] [CharZero K] [Field k]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hsp : (f.map (algebraMap ℤ K)).Splits) (ρ : 𝓞 K →+* k) :
    f.map (Int.castRingHom k) = ∏ x : f.rootSet K, (X - C (ρ (rootInteger f hm x))) := by
  classical
  simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_map, RingHom.eq_intCast'] using
      congrArg (Polynomial.map ρ) (map_eq_prod_rootInteger f hm hs hsp)

lemma reduction_injective {K k : Type*} [Field K] [CharZero K] [Field k]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hsp : (f.map (algebraMap ℤ K)).Splits) (ρ : 𝓞 K →+* k)
    (hred : (f.map (Int.castRingHom k)).Separable) :
    Function.Injective (fun x : f.rootSet K => ρ (rootInteger f hm x)) := by
  rw [reduction_factorization f hm hs hsp ρ] at hred
  exact hred.injective_of_prod_X_sub_C

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_FrobeniusRoots
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen




theorem numberField_frobenius (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (p : ℕ) [Fact p.Prime] :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ σ : Gal(K/ℚ), ∀ x : 𝓞 K,
        Ideal.Quotient.mk P (((galRestrict ℤ ℚ K (𝓞 K)) σ) x) =
          (Ideal.Quotient.mk P x) ^ p := by
  let := IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K)
  let := Algebra.isInvariant_of_isGalois ℤ ℚ K (𝓞 K)
  obtain ⟨P, hP, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  let := hP
  let := hOver
  let : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.IsMaximal.ne_bot_of_isIntegral_int P)
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  refine ⟨P, hP, hOver, σ, ?_⟩
  intro x
  have h := hσ.mk_apply x
  rw [← Ideal.over_def P (Ideal.span {(p : ℤ)}), Int.card_ideal_quot] at h
  exact h

end DimensionTen

end
end

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma quotient_charP {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : CharP (𝓞 K ⧸ P) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  have hp : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P :=
    (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.subset_span (by simp))
  simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hp)

lemma rootInteger_gal {K : Type*} [Field K] [NumberField K]
    (f : ℤ[X]) (hm : f.Monic) (σ : Gal(K/ℚ)) (x : f.rootSet K) :
    rootInteger f hm (σ • x) = (galRestrict ℤ ℚ K (𝓞 K) σ) (rootInteger f hm x) := by
  apply RingOfIntegers.coe_injective
  rw [algebraMap_galRestrict_apply]
  rfl

lemma root_reduction_frobenius {K : Type*} [Field K] [NumberField K]
    (f : ℤ[X]) (hm : f.Monic) (p : ℕ) (P : Ideal (𝓞 K)) (σ : Gal(K/ℚ))
    (hσ : ∀ x : 𝓞 K, Ideal.Quotient.mk P ((galRestrict ℤ ℚ K (𝓞 K) σ) x) =
        (Ideal.Quotient.mk P x) ^ p) (x : f.rootSet K) :
    Ideal.Quotient.mk P (rootInteger f hm (σ • x)) =
        (Ideal.Quotient.mk P (rootInteger f hm x)) ^ p := by
  rw [rootInteger_gal, hσ]

lemma iterate_pow_perm {ι R : Type*} [Monoid R] (σ : Equiv.Perm ι) (r : ι → R)
    (p : ℕ) (h : ∀ i, r (σ i) = r i ^ p) (n : ℕ) :
    ∀ i, r ((σ ^ n) i) = r i ^ (p ^ n) := by
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    rw [pow_succ', Equiv.Perm.mul_apply, h, ih, ← pow_mul, pow_succ]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers01
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow1_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z + (139 : R) * pow1_2_mul_t z := by
  simp only [u0, pow1_2_q, f, pow1_2, pow1_2_mul_t]
  
  ring

theorem pow1_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_2_mul_integer z


theorem pow1_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z * u0 z = pow1_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_2_mul z


theorem pow1_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 2 = pow1_2 z := by
  calc
    _ = u0 z ^ 1 * u0 z ^ 1 := by ring
    _ = u0 z * u0 z := by simp only [pow_one]
    _ = _ := pow1_2_root z hz


theorem pow1_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z + (139 : R) * pow1_4_mul_t z := by
  simp only [pow1_2, pow1_4_q, f, pow1_4, pow1_4_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_4_mul_integer z


theorem pow1_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_2 z * pow1_2 z = pow1_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_4_mul z


theorem pow1_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 4 = pow1_4 z := by
  calc
    _ = u0 z ^ 2 * u0 z ^ 2 := by ring
    _ = pow1_2 z * pow1_2 z := by rw [pow1_2_pow z hz]
    _ = _ := pow1_4_root z hz


theorem pow1_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z + (139 : R) * pow1_8_mul_t z := by
  simp only [pow1_4, pow1_8_q, f, pow1_8, pow1_8_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_8_mul_integer z


theorem pow1_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_4 z * pow1_4 z = pow1_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_8_mul z


theorem pow1_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 8 = pow1_8 z := by
  calc
    _ = u0 z ^ 4 * u0 z ^ 4 := by ring
    _ = pow1_4 z * pow1_4 z := by rw [pow1_4_pow z hz]
    _ = _ := pow1_8_root z hz


theorem pow1_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z + (139 : R) * pow1_16_mul_t z := by
  simp only [pow1_8, pow1_16_q, f, pow1_16, pow1_16_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_16_mul_integer z


theorem pow1_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_8 z * pow1_8 z = pow1_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_16_mul z


theorem pow1_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 16 = pow1_16 z := by
  calc
    _ = u0 z ^ 8 * u0 z ^ 8 := by ring
    _ = pow1_8 z * pow1_8 z := by rw [pow1_8_pow z hz]
    _ = _ := pow1_16_root z hz


theorem pow1_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_16 z * u0 z = pow1_17_q z * f z + pow1_17 z + (139 : R) * pow1_17_mul_t z := by
  simp only [pow1_16, u0, pow1_17_q, f, pow1_17, pow1_17_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_16 z * u0 z = pow1_17_q z * f z + pow1_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_17_mul_integer z


theorem pow1_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_16 z * u0 z = pow1_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_17_mul z


theorem pow1_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 17 = pow1_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow1_16_pow z hz]
  exact pow1_17_root z hz


theorem pow1_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_17 z * pow1_17 z = pow1_34_q z * f z + pow1_34 z + (139 : R) * pow1_34_mul_t z := by
  simp only [pow1_17, pow1_34_q, f, pow1_34, pow1_34_mul_t]
  
  ring

theorem pow1_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_17 z * pow1_17 z = pow1_34_q z * f z + pow1_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_34_mul_integer z


theorem pow1_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_17 z * pow1_17 z = pow1_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_34_mul z


theorem pow1_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 34 = pow1_34 z := by
  calc
    _ = u0 z ^ 17 * u0 z ^ 17 := by ring
    _ = pow1_17 z * pow1_17 z := by rw [pow1_17_pow z hz]
    _ = _ := pow1_34_root z hz


theorem pow1_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_34 z * pow1_34 z = pow1_68_q z * f z + pow1_68 z + (139 : R) * pow1_68_mul_t z := by
  simp only [pow1_34, pow1_68_q, f, pow1_68, pow1_68_mul_t]
  
  ring

theorem pow1_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_34 z * pow1_34 z = pow1_68_q z * f z + pow1_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_68_mul_integer z


theorem pow1_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_34 z * pow1_34 z = pow1_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_68_mul z


theorem pow1_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 68 = pow1_68 z := by
  calc
    _ = u0 z ^ 34 * u0 z ^ 34 := by ring
    _ = pow1_34 z * pow1_34 z := by rw [pow1_34_pow z hz]
    _ = _ := pow1_68_root z hz


theorem pow1_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_68 z * u0 z = pow1_69_q z * f z + pow1_69 z + (139 : R) * pow1_69_mul_t z := by
  simp only [pow1_68, u0, pow1_69_q, f, pow1_69, pow1_69_mul_t]
  
  ring

theorem pow1_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_68 z * u0 z = pow1_69_q z * f z + pow1_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_69_mul_integer z


theorem pow1_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_68 z * u0 z = pow1_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_69_mul z


theorem pow1_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 69 = pow1_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow1_68_pow z hz]
  exact pow1_69_root z hz


theorem pow1_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_69 z * pow1_69 z = pow1_138_q z * f z + pow1_138 z + (139 : R) * pow1_138_mul_t z := by
  simp only [pow1_69, pow1_138_q, f, pow1_138, pow1_138_mul_t]
  
  ring

theorem pow1_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_69 z * pow1_69 z = pow1_138_q z * f z + pow1_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_138_mul_integer z


theorem pow1_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_69 z * pow1_69 z = pow1_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_138_mul z


theorem pow1_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 138 = pow1_138 z := by
  calc
    _ = u0 z ^ 69 * u0 z ^ 69 := by ring
    _ = pow1_69 z * pow1_69 z := by rw [pow1_69_pow z hz]
    _ = _ := pow1_138_root z hz


theorem pow1_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_138 z * u0 z = pow1_139_q z * f z + pow1_139 z + (139 : R) * pow1_139_mul_t z := by
  simp only [pow1_138, u0, pow1_139_q, f, pow1_139, pow1_139_mul_t]
  
  ring

theorem pow1_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_138 z * u0 z = pow1_139_q z * f z + pow1_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_139_mul_integer z


theorem pow1_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_138 z * u0 z = pow1_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_139_mul z


theorem pow1_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 139 = pow1_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow1_138_pow z hz]
  exact pow1_139_root z hz


theorem iterate1 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 1) = u1 z := by
  calc
    _ = (z ^ (139 ^ 0)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u0 z ^ 139 := congrArg (fun x : R => x ^ 139) (initial z )
    _ = _ := pow1_139_pow z hz


end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers10
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow19_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u18 z * u18 z = pow19_2_q z * f z + pow19_2 z + (139 : R) * pow19_2_mul_t z := by
  simp only [u18, pow19_2_q, f, pow19_2, pow19_2_mul_t]
  simp only [pow18_139]
  ring

theorem pow19_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u18 z * u18 z = pow19_2_q z * f z + pow19_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_2_mul_integer z


theorem pow19_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z * u18 z = pow19_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_2_mul z


theorem pow19_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 2 = pow19_2 z := by
  calc
    _ = u18 z ^ 1 * u18 z ^ 1 := by ring
    _ = u18 z * u18 z := by simp only [pow_one]
    _ = _ := pow19_2_root z hz


theorem pow19_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_2 z * pow19_2 z = pow19_4_q z * f z + pow19_4 z + (139 : R) * pow19_4_mul_t z := by
  simp only [pow19_2, pow19_4_q, f, pow19_4, pow19_4_mul_t]
  
  ring

theorem pow19_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_2 z * pow19_2 z = pow19_4_q z * f z + pow19_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_4_mul_integer z


theorem pow19_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_2 z * pow19_2 z = pow19_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_4_mul z


theorem pow19_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 4 = pow19_4 z := by
  calc
    _ = u18 z ^ 2 * u18 z ^ 2 := by ring
    _ = pow19_2 z * pow19_2 z := by rw [pow19_2_pow z hz]
    _ = _ := pow19_4_root z hz


theorem pow19_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_4 z * pow19_4 z = pow19_8_q z * f z + pow19_8 z + (139 : R) * pow19_8_mul_t z := by
  simp only [pow19_4, pow19_8_q, f, pow19_8, pow19_8_mul_t]
  
  ring

theorem pow19_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_4 z * pow19_4 z = pow19_8_q z * f z + pow19_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_8_mul_integer z


theorem pow19_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_4 z * pow19_4 z = pow19_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_8_mul z


theorem pow19_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 8 = pow19_8 z := by
  calc
    _ = u18 z ^ 4 * u18 z ^ 4 := by ring
    _ = pow19_4 z * pow19_4 z := by rw [pow19_4_pow z hz]
    _ = _ := pow19_8_root z hz


theorem pow19_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_8 z * pow19_8 z = pow19_16_q z * f z + pow19_16 z + (139 : R) * pow19_16_mul_t z := by
  simp only [pow19_8, pow19_16_q, f, pow19_16, pow19_16_mul_t]
  
  ring

theorem pow19_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_8 z * pow19_8 z = pow19_16_q z * f z + pow19_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_16_mul_integer z


theorem pow19_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_8 z * pow19_8 z = pow19_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_16_mul z


theorem pow19_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 16 = pow19_16 z := by
  calc
    _ = u18 z ^ 8 * u18 z ^ 8 := by ring
    _ = pow19_8 z * pow19_8 z := by rw [pow19_8_pow z hz]
    _ = _ := pow19_16_root z hz


theorem pow19_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_16 z * u18 z = pow19_17_q z * f z + pow19_17 z + (139 : R) * pow19_17_mul_t z := by
  simp only [pow19_16, u18, pow19_17_q, f, pow19_17, pow19_17_mul_t]
  simp only [pow18_139]
  ring

theorem pow19_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_16 z * u18 z = pow19_17_q z * f z + pow19_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_17_mul_integer z


theorem pow19_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_16 z * u18 z = pow19_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_17_mul z


theorem pow19_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 17 = pow19_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow19_16_pow z hz]
  exact pow19_17_root z hz


theorem pow19_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_17 z * pow19_17 z = pow19_34_q z * f z + pow19_34 z + (139 : R) * pow19_34_mul_t z := by
  simp only [pow19_17, pow19_34_q, f, pow19_34, pow19_34_mul_t]
  
  ring

theorem pow19_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_17 z * pow19_17 z = pow19_34_q z * f z + pow19_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_34_mul_integer z


theorem pow19_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_17 z * pow19_17 z = pow19_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_34_mul z


theorem pow19_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 34 = pow19_34 z := by
  calc
    _ = u18 z ^ 17 * u18 z ^ 17 := by ring
    _ = pow19_17 z * pow19_17 z := by rw [pow19_17_pow z hz]
    _ = _ := pow19_34_root z hz


theorem pow19_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_34 z * pow19_34 z = pow19_68_q z * f z + pow19_68 z + (139 : R) * pow19_68_mul_t z := by
  simp only [pow19_34, pow19_68_q, f, pow19_68, pow19_68_mul_t]
  
  ring

theorem pow19_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_34 z * pow19_34 z = pow19_68_q z * f z + pow19_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_68_mul_integer z


theorem pow19_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_34 z * pow19_34 z = pow19_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_68_mul z


theorem pow19_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 68 = pow19_68 z := by
  calc
    _ = u18 z ^ 34 * u18 z ^ 34 := by ring
    _ = pow19_34 z * pow19_34 z := by rw [pow19_34_pow z hz]
    _ = _ := pow19_68_root z hz


theorem pow19_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_68 z * u18 z = pow19_69_q z * f z + pow19_69 z + (139 : R) * pow19_69_mul_t z := by
  simp only [pow19_68, u18, pow19_69_q, f, pow19_69, pow19_69_mul_t]
  simp only [pow18_139]
  ring

theorem pow19_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_68 z * u18 z = pow19_69_q z * f z + pow19_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_69_mul_integer z


theorem pow19_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_68 z * u18 z = pow19_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_69_mul z


theorem pow19_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 69 = pow19_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow19_68_pow z hz]
  exact pow19_69_root z hz


theorem pow19_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_69 z * pow19_69 z = pow19_138_q z * f z + pow19_138 z + (139 : R) * pow19_138_mul_t z := by
  simp only [pow19_69, pow19_138_q, f, pow19_138, pow19_138_mul_t]
  
  ring

theorem pow19_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_69 z * pow19_69 z = pow19_138_q z * f z + pow19_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_138_mul_integer z


theorem pow19_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_69 z * pow19_69 z = pow19_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_138_mul z


theorem pow19_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 138 = pow19_138 z := by
  calc
    _ = u18 z ^ 69 * u18 z ^ 69 := by ring
    _ = pow19_69 z * pow19_69 z := by rw [pow19_69_pow z hz]
    _ = _ := pow19_138_root z hz


theorem pow19_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_138 z * u18 z = pow19_139_q z * f z + pow19_139 z + (139 : R) * pow19_139_mul_t z := by
  simp only [pow19_138, u18, pow19_139_q, f, pow19_139, pow19_139_mul_t]
  simp only [pow18_139, u0]
  ring

theorem pow19_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_138 z * u18 z = pow19_139_q z * f z + pow19_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_139_mul_integer z


theorem pow19_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_138 z * u18 z = pow19_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_139_mul z


theorem pow19_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 139 = pow19_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow19_138_pow z hz]
  exact pow19_139_root z hz


theorem iterate19 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 19) = u19 z := by
  calc
    _ = (z ^ (139 ^ 18)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u18 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate18 z hz)
    _ = _ := pow19_139_pow z hz

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Result
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem bezout1_integer {R : Type*} [CommRing R] (z : R) :
    a1 z * f z + b1 z * (u1 z - z) = g1 z + (139 : R) * bezout1_t z := by
  simp only [a1, b1, f, u1, g1, bezout1_t]
  simp only [pow1_139]
  ring

theorem bezout1 {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    a1 z * f z + b1 z * (u1 z - z) = g1 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using bezout1_integer z


theorem factor1_f_integer {R : Type*} [CommRing R] (z : R) :
    f z = g1 z * div1_f z + (139 : R) * factor1_f_t z := by
  simp only [f, g1, div1_f, factor1_f_t]
  
  ring

theorem factor1_f {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    f z = g1 z * div1_f z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using factor1_f_integer z


theorem factor1_u1_integer {R : Type*} [CommRing R] (z : R) :
    (u1 z - z) = g1 z * div1_u1 z + (139 : R) * factor1_u1_t z := by
  simp only [u1, g1, div1_u1, factor1_u1_t]
  simp only [pow1_139]
  ring

theorem factor1_u1 {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    (u1 z - z) = g1 z * div1_u1 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using factor1_u1_integer z


theorem separable_bezout_integer {R : Type*} [CommRing R] (z : R) :
    da z * f z + db z * df z = 1 + (139 : R) * separable_bezout_t z := by
  simp only [da, db, df, f, separable_bezout_t]
  
  ring

theorem separable_bezout {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    da z * f z + db z * df z = 1 := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using separable_bezout_integer z

end DimensionTen.Mod139

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod139

lemma horner_monic_degree {R : Type*} [CommRing R] [Nontrivial R] {p : R[X]} {n : ℕ}
    (hp : p.IsMonicOfDegree n) (a : R) :
    (C a + X * p).IsMonicOfDegree (n+1) := by
  apply (isMonicOfDegree_iff _ _).mpr
  constructor
  · rw [natDegree_C_add, monic_X.natDegree_mul hp.monic, natDegree_X, hp.natDegree_eq]
    omega
  · simp only [coeff_add, coeff_C, Nat.add_one_ne_zero, ite_false, zero_add, coeff_X_mul]
    simpa only [hp.natDegree_eq] using hp.monic.coeff_natDegree

lemma horner_zero_degree {R : Type*} [CommRing R] [Nontrivial R] {p : R[X]} {n : ℕ}
    (hp : p.IsMonicOfDegree n) : (0 + X * p).IsMonicOfDegree (n+1) := by
  simpa only [C_0] using horner_monic_degree hp 0

lemma degree_g {R : Type*} [CommRing R] [Nontrivial R] :
    (g1 (X : R[X])).IsMonicOfDegree 1 := by
  unfold g1
  repeat' first | apply horner_monic_degree | apply horner_zero_degree
  exact ⟨natDegree_one, monic_one⟩

lemma map_f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (f z) = f (φ z) := by
  simp only [f, map_add, map_mul, map_ofNat, map_one, map_zero]

lemma map_g1 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (g1 z) = g1 (φ z) := by
  simp only [g1, map_add, map_mul, map_ofNat, map_one]

lemma derivative_identity {R : Type*} [CommRing R] :
    Polynomial.derivative (f (X : R[X])) = df X + (139 : R[X]) * derivative_extra X := by
  simp only [f, df, derivative_extra, derivative_add, derivative_mul, derivative_X,
    derivative_ofNat, derivative_one, derivative_zero]
  ring

lemma separable_f {k : Type*} [Field k] [CharP k 139] :
    (f (X : k[X])).Separable := by
  change IsCoprime _ _
  have h : (139 : k[X]) = 0 := CharP.cast_eq_zero _ 139
  rw [derivative_identity, h, zero_mul, add_zero]
  exact ⟨da X, db X, separable_bezout _⟩

lemma fixed_iff_g_zero {k : Type*} [Field k] [CharP k 139] (z : k) (hz : f z = 0) :
    z ^ (139 ^ 1) = z ↔ g1 z = 0 := by
  rw [iterate1 z hz]
  constructor
  · intro h
    have hb := bezout1 z
    simpa only [hz, mul_zero, h, sub_self, zero_add] using hb.symm
  · intro h
    apply sub_eq_zero.mp
    rw [factor1_u1, h, zero_mul]

end DimensionTen.Mod139

end
end

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_RootPermutation
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial
namespace DimensionTen


theorem card_fixed_of_factor {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    (r : ι → k) (hr : Function.Injective r) (σ : Equiv.Perm ι)
    (f g : k[X]) (hf : f = ∏ i, (X - C (r i))) (hs : f.Separable)
    (hd : g ∣ f) (hroot : ∀ i, g.eval (r i) = 0 ↔ σ i = i) :
    Fintype.card {i : ι // σ i = i} = g.natDegree := by
  classical
  have hf0 : f ≠ 0 := by rw [hf]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)
  have hg0 : g ≠ 0 := ne_zero_of_dvd_ne_zero hf0 hd
  have hsplit : f.Splits := by rw [hf]; exact Splits.prod (fun _ _ => Splits.X_sub_C _)
  have hgr : ∀ x : k, g.eval x = 0 → ∃ i, r i = x := by
    intro x hx
    have hx' : f.eval x = 0 := by
      obtain ⟨q, rfl⟩ := hd
      simp [eval_mul, hx]
    rw [hf, eval_prod] at hx'
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hx'
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
    exact ⟨i, hi.symm⟩
  let u : {i : ι // σ i = i} → g.rootSet k :=
    fun i => ⟨r i, mem_rootSet.mpr ⟨hg0, by simpa using (hroot i).mpr i.property⟩⟩
  have hu : Function.Injective u := by
    intro i j h
    apply Subtype.ext
    apply hr
    exact congrArg Subtype.val h
  have hus : Function.Surjective u := by
    intro x
    have hx : g.eval (x : k) = 0 := by simpa using (mem_rootSet.mp x.property).2
    obtain ⟨i, hi⟩ := hgr x hx
    refine ⟨⟨i, (hroot i).mp (hi ▸ hx)⟩, ?_⟩
    exact Subtype.ext hi
  let e := Equiv.ofBijective u ⟨hu, hus⟩
  rw [Fintype.card_congr e]
  exact card_rootSet_eq_natDegree (hs.of_dvd hd) (by simpa using (hsplit.of_dvd hf0 hd))

lemma cycle_of_pow_eq_one_card_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 20) (σ : Equiv.Perm ι)
    (hpow : σ ^ 19 = 1) (hfix : Fintype.card {i : ι // σ i = i} = 1) :
    σ.IsCycle ∧ σ.support.card = 19 := by
  have hc : σ.support.card = 19 := by
    have h := Fintype.card_subtype_compl (fun i => σ i = i)
    rw [hcard, hfix] at h
    simpa only [Fintype.card_subtype, Equiv.Perm.support] using h
  have hne : σ ≠ 1 := by intro h; simp [h] at hc
  have hord : orderOf σ = 19 := by
    have hd := orderOf_dvd_of_pow_eq_one hpow
    have hp : Nat.Prime 19 := by decide
    exact (hp.eq_one_or_self_of_dvd _ hd).resolve_left (by simpa using hne)
  exact ⟨Equiv.Perm.isCycle_of_prime_order (by rw [hord]; decide) (by rw [hc, hord]; omega), hc⟩

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_ModularPermutations
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Equiv Equiv.Perm MulAction
namespace DimensionTen


theorem full_symmetric_of_nineteen_cycle {α : Type*} [Fintype α] [DecidableEq α]
    (H : Subgroup (Perm α)) (hc : Fintype.card α = 20)
    [IsPretransitive H α]
    (σ : Perm α) (hσ : σ ∈ H) (hcycle : σ.IsCycle) (hs : σ.support.card = 19)
    (τ : Perm α) (hτ : τ ∈ H) (hswap : τ.IsSwap) : H = ⊤ := by
  classical
  have ht : (σ.supportᶜ).card = 1 := by rw [Finset.card_compl, hs, hc]
  obtain ⟨a₀, ha₀⟩ := Finset.card_eq_one.mp ht
  have hm (a : α) : σ a ≠ a ↔ a ≠ a₀ := by
    have h := congrArg (fun s : Finset α => a ∈ s) ha₀
    simpa only [Finset.mem_compl, mem_support, not_not, Finset.mem_singleton] using not_congr (iff_of_eq h)
  have hfix : σ a₀ = a₀ := not_ne_iff.mp ((hm a₀).not.mpr (by simp))
  have htwo : IsMultiplyPretransitive H α 2 := by
    rw [is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg⟩ := exists_smul_eq (M := H) a a₀
    obtain ⟨h, hh⟩ := exists_smul_eq (M := H) c a₀
    have hgb : σ (g • b) ≠ g • b := (hm _).mpr (by
      intro hb; exact hab ((MulAction.injective g) (hg.trans hb.symm)))
    have hhd : σ (h • d) ≠ h • d := (hm _).mpr (by
      intro hd; exact hcd ((MulAction.injective h) (hh.trans hd.symm)))
    obtain ⟨n, hn⟩ := hcycle.exists_pow_eq hgb hhd
    refine ⟨h⁻¹ * (⟨σ, hσ⟩ : H) ^ n * g, ?_, ?_⟩
    · simp only [mul_smul, hg]
      have hhfix : ((⟨σ, hσ⟩ : H) ^ n) • a₀ = a₀ := by
        exact pow_apply_eq_self_of_apply_eq_self hfix n
      rw [hhfix, ← hh, inv_smul_smul]
    · simp only [mul_smul]
      change h⁻¹ • ((σ ^ n) (g • b)) = d
      rw [hn, inv_smul_smul]
  exact subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (isPreprimitive_of_is_two_pretransitive htwo) τ hswap hτ

end DimensionTen

end
end

section
noncomputable section
open Polynomial
namespace DimensionTen

lemma root_of_product {k ι : Type*} [Field k] [Fintype ι]
    (r : ι → k) (f : k[X]) (hf : f = ∏ i, (X - C (r i))) (i : ι) :
    f.eval (r i) = 0 := by
  classical
  rw [hf, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

lemma eval_mod139_f {k : Type*} [CommRing k] (x : k) :
    (Mod139.f (X : k[X])).eval x = Mod139.f x :=
  (Mod139.map_f (evalRingHom x) X).trans (congrArg Mod139.f (eval_X))

lemma eval_mod139_g {k : Type*} [CommRing k] (x : k) :
    (Mod139.g1 (X : k[X])).eval x = Mod139.g1 x :=
  (Mod139.map_g1 (evalRingHom x) X).trans (congrArg Mod139.g1 (eval_X))

lemma fixed_mod139 {k ι : Type*} [Field k] [CharP k 139] [Fintype ι] [DecidableEq ι]
    (r : ι → k) (hinj : Function.Injective r) (π : Equiv.Perm ι)
    (hfact : Mod139.f X = ∏ i, (X - C (r i)))
    (hfrob : ∀ i, r (π i) = r i ^ 139) :
    Fintype.card {i : ι // (π ^ 1) i = i} = 1 := by
  have hfroot (i : ι) : Mod139.f (r i) = 0 := by
    rw [← eval_mod139_f]; exact root_of_product r _ hfact i
  have hfix (i : ι) : (Mod139.g1 (X : k[X])).eval (r i) = 0 ↔ (π ^ 1) i = i := by
    rw [eval_mod139_g, ← Mod139.fixed_iff_g_zero _ (hfroot i),
      ← iterate_pow_perm π r 139 hfrob 1 i, hinj.eq_iff]
  have hd : Mod139.g1 (X : k[X]) ∣ Mod139.f X :=
    ⟨Mod139.div1_f X, Mod139.factor1_f X⟩
  exact (card_fixed_of_factor r hinj (π ^ 1) _ _ hfact Mod139.separable_f hd hfix).trans
    Mod139.degree_g.natDegree_eq

lemma pow_mod139 {k ι : Type*} [Field k] [CharP k 139] [Fintype ι]
    (r : ι → k) (hinj : Function.Injective r) (π : Equiv.Perm ι)
    (hfact : Mod139.f X = ∏ i, (X - C (r i)))
    (hfrob : ∀ i, r (π i) = r i ^ 139) : π ^ 19 = 1 := by
  ext i
  apply hinj
  rw [iterate_pow_perm π r 139 hfrob]
  have hr : Mod139.f (r i) = 0 := by
    rw [← eval_mod139_f]; exact root_of_product r _ hfact i
  rw [Mod139.iterate19 _ hr]
  
  simp [Mod139.u19, Mod139.u0]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_GaloisCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma reduction_eq_139 {k : Type*} [Field k] [CharP k 139]
    (f : ℤ[X]) (h : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
    f.map (Int.castRingHom k) = Mod139.f X := by
  let φ := ZMod.castHom (dvd_refl 139) k
  have hmap : map φ (Mod139.f X) = Mod139.f X := by
    change mapRingHom φ (Mod139.f X) = _
    exact (Mod139.map_f (mapRingHom φ) X).trans (congrArg Mod139.f (map_X φ))
  have := congrArg (map φ) h
  rw [map_map] at this
  have he : φ.comp (Int.castRingHom (ZMod _)) = Int.castRingHom k := RingHom.eq_intCast' _
  rw [he] at this
  exact this.trans hmap

lemma irr_rational_of_mod41 (f : ℤ[X]) (hm : f.Monic)
    (h : f.map (Int.castRingHom (ZMod 41)) = Mod41.f X) :
    Irreducible (f.map (algebraMap ℤ ℚ)) := by
  apply hm.irreducible_iff_irreducible_map_fraction_map.mp
  apply Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 41)) f hm
  rw [h]
  exact Mod41.irreducible_f

section Roots
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [DecidableEq K]
variable (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hp : (f.map (algebraMap ℤ K)).Splits)
    (hc : Fintype.card (f.rootSet K) = 20)

include hm hs hp hc in
lemma exists_nineteen_cycle_of_mod139
    (h139 : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
    ∃ σ : Gal(K/ℚ), (MulAction.toPerm σ : Equiv.Perm (f.rootSet K)).IsCycle ∧
      (MulAction.toPerm σ : Equiv.Perm (f.rootSet K)).support.card = 19 := by
  classical
  let : Fact (Nat.Prime 139) := ⟨by decide⟩
  obtain ⟨P, hP, hOver, σ, hσ⟩ := numberField_frobenius K 139
  let := hP
  let := hOver
  let k := 𝓞 K ⧸ P
  let : Field k := Ideal.Quotient.field P
  let : CharP k 139 := quotient_charP 139 P
  let ρ := Ideal.Quotient.mk P
  let r : f.rootSet K → k := fun x => ρ (rootInteger f hm x)
  let π : Equiv.Perm (f.rootSet K) := MulAction.toPerm σ
  have hred := reduction_eq_139 (k := k) f h139
  have hsep : (f.map (Int.castRingHom k)).Separable := by
    rw [hred]; exact Mod139.separable_f
  have hinj : Function.Injective r := reduction_injective f hm hs hp ρ hsep
  have hfact : Mod139.f X = ∏ i, (X - C (r i)) :=
    hred ▸ reduction_factorization f hm hs hp ρ
  have hfrob (i : f.rootSet K) : r (π i) = r i ^ 139 :=
    root_reduction_frobenius f hm 139 P σ hσ i
  have h1 : Fintype.card {i : f.rootSet K // π i = i} = 1 := by
    simpa only [pow_one] using fixed_mod139 r hinj π hfact hfrob
  exact ⟨σ, cycle_of_pow_eq_one_card_fixed hc π (pow_mod139 r hinj π hfact hfrob) h1⟩

include hm in
omit [IsGalois ℚ K] [DecidableEq K] in
lemma root_minpoly (hirr : Irreducible (f.map (algebraMap ℤ ℚ))) (x : f.rootSet K) :
    minpoly ℚ (x : K) = f.map (algebraMap ℤ ℚ) := by
  have hx : (aeval (x : K)) (f.map (algebraMap ℤ ℚ)) = 0 := by
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq ℤ ℚ K]
    exact (mem_rootSet.mp x.property).2
  have he := minpoly.eq_of_irreducible hirr hx
  simpa only [(hm.map (algebraMap ℤ ℚ)).leadingCoeff, inv_one, C_1, mul_one] using he.symm

include hm in
omit [DecidableEq K] in
lemma root_action_pretransitive (hirr : Irreducible (f.map (algebraMap ℤ ℚ))) :
    MulAction.IsPretransitive Gal(K/ℚ) (f.rootSet K) := by
  constructor
  intro x y
  have hh : minpoly ℚ (y : K) = minpoly ℚ (x : K) :=
    (root_minpoly f hm hirr y).trans (root_minpoly f hm hirr x).symm
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit K).mp hh
  exact ⟨σ, Subtype.ext hσ⟩

include hm hs hp hc in
lemma root_action_full_symmetric
    (h41 : f.map (Int.castRingHom (ZMod 41)) = Mod41.f X)
    (h131 : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X)
    (h139 : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
    Function.Surjective (MulAction.toPermHom Gal(K/ℚ) (f.rootSet K)) := by
  classical
  let φ := MulAction.toPermHom Gal(K/ℚ) (f.rootSet K)
  let H := φ.range
  let : MulAction.IsPretransitive Gal(K/ℚ) (f.rootSet K) :=
    root_action_pretransitive f hm (irr_rational_of_mod41 f hm h41)
  let : MulAction.IsPretransitive H (f.rootSet K) := by
    constructor
    intro a b
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (M := Gal(K/ℚ)) a b
    exact ⟨⟨φ σ, ⟨σ, rfl⟩⟩, hσ⟩
  obtain ⟨σ, hσ, hcσ⟩ := exists_nineteen_cycle_of_mod139 f hm hs hp hc h139
  obtain ⟨τ, hτ⟩ := exists_swap_of_mod131 f hm hs hp hc h131
  have htop : H = ⊤ := full_symmetric_of_nineteen_cycle H hc (φ σ) ⟨σ, rfl⟩ hσ hcσ
    (φ (τ ^ 17)) ⟨τ ^ 17, rfl⟩ hτ
  exact MonoidHom.range_eq_top.mp htop

end Roots
end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_GaloisField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

lemma galois_permute (π : Equiv.Perm (Fin 20)) :
    ∃ σ : Gal(K/ℚ), ∀ i, σ.toAlgHom.comp (embeddingsK i) = embeddingsK (π i) := by
  classical
  let e := embeddingsK.trans (embeddingRootEquiv (R := K))
  let p : Equiv.Perm (F.rootSet K) := (e.symm.trans π).trans e
  obtain ⟨σ, hσ⟩ := root_action_full_symmetric F F_monic F_separable_K F_splits_K
    roots_card_K F_reduction_41 F_reduction_131 F_reduction_139 p
  refine ⟨σ, fun i => ?_⟩
  apply (embeddingRootEquiv (R := K)).injective
  apply Subtype.ext
  have hi := congrArg (fun q : Equiv.Perm (F.rootSet K) => (q (e i) : K)) hσ
  change σ (e i : K) = (e (π (e.symm (e i))) : K) at hi
  rw [e.symm_apply_apply] at hi
  exact hi

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_IndependentMinor
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Arithmetic

lemma independent_minor {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : Function.Surjective A.mulVec) :
    ∃ a : Fin m → Fin n, Function.Injective a ∧ (A.submatrix id a).det ≠ 0 := by
  classical
  have hsp : Submodule.span K (Set.range A.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr hA
  obtain ⟨κ, a, ha, hs, hl⟩ := exists_linearIndependent' K A.col
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let b : Module.Basis κ K (Fin m → K) := Module.Basis.mk hl (by rw [hs, hsp])
  have hc : Fintype.card κ = m := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e : Fin m ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hh : LinearIndependent K (A.submatrix id (a ∘ e)).col := hl.comp e e.injective
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hh))

lemma restrict_rows_surjective {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0)
    (r : Fin m → Fin n) (hr : Function.Injective r) :
    Function.Surjective (A.submatrix r id).mulVec := by
  classical
  intro v
  let w : Fin n → K := Function.extend r v 0
  have hw : w ∘ r = v := Function.extend_comp hr _ _
  obtain ⟨u, hu⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA))) w
  refine ⟨u, ?_⟩
  ext i
  exact (congrFun hu (r i)).trans (congrFun hw i)

end DimensionTen.Arithmetic

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_EvaluationMinors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

lemma evaluationMatrix_map : evaluationMatrix.map complexEmbedding =
    Algebra.embeddingsMatrixReindex ℚ ℂ basis embeddingsC := by
  ext i j
  change complexEmbedding (embeddingsK j (low alpha i)) = embeddingsC j (basis i)
  rw [basis_eq]
  rfl

lemma evaluationMatrix_det_ne : evaluationMatrix.det ≠ 0 := by
  intro hz
  have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ basis embeddingsC
  have hc : (Algebra.embeddingsMatrixReindex ℚ ℂ basis embeddingsC).det = 0 := by
    rw [← evaluationMatrix_map]
    erw [← complexEmbedding.map_det, hz, map_zero]
  rw [hc, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hd
  exact Algebra.discr_not_zero_of_basis ℚ basis ((algebraMap ℚ ℂ).injective (hd.trans (map_zero _).symm))

lemma some_ten_minor : ∃ a : Fin 10 → Fin 20, Function.Injective a ∧
    (evaluationMatrix.submatrix firstTen a).det ≠ 0 := by
  obtain ⟨a, ha, hd⟩ := Arithmetic.independent_minor
    (evaluationMatrix.submatrix firstTen id)
    (Arithmetic.restrict_rows_surjective evaluationMatrix evaluationMatrix_det_ne
      firstTen (Fin.castLE_injective _))
  exact ⟨a, ha, hd⟩

lemma every_ten_minor (b : Fin 10 → Fin 20) (hb : Function.Injective b) :
    (evaluationMatrix.submatrix firstTen b).det ≠ 0 := by
  classical
  obtain ⟨a, ha, hd⟩ := some_ten_minor
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair a b ha hb
  obtain ⟨σ, hσ⟩ := galois_permute π
  have he : (evaluationMatrix.submatrix firstTen a).map σ.toRingHom =
      evaluationMatrix.submatrix firstTen b := by
    ext i j
    change σ (embeddingsK (a j) (low alpha (firstTen i))) =
      embeddingsK (b j) (low alpha (firstTen i))
    have hh := congrArg (fun τ : L →ₐ[ℚ] K => τ (low alpha (firstTen i))) (hσ (a j))
    rw [hπ] at hh
    exact hh
  rw [← he]
  erw [← σ.map_det]
  exact (map_ne_zero σ.toRingHom).mpr hd

lemma ten_complex_minor (b : Fin 10 → Fin 20) (hb : Function.Injective b) :
    Matrix.det (fun i j : Fin 10 => low (points (b j)) (firstTen i)) ≠ 0 := by
  have he : (evaluationMatrix.submatrix firstTen b).map complexEmbedding =
      (fun i j : Fin 10 => low (points (b j)) (firstTen i)) := by
    ext i j
    change embeddingsC (b j) (low alpha (firstTen i)) = _
    exact low_map (embeddingsC (b j)).toRingHom alpha (firstTen i)
  rw [← he]
  erw [← complexEmbedding.map_det]
  exact (map_ne_zero complexEmbedding).mpr (every_ten_minor b hb)

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_QuadraticBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma low_quadratic (t : Fin 3 → ℂ) (i : Fin 10) :
    low t (Fin.castLE (by decide) i) =
      chart t (quadraticEquiv i).val.1 * chart t (quadraticEquiv i).val.2 := by
  change _ = chart t (quadraticPairs i).1 * chart t (quadraticPairs i).2
  have hc2 : Fin.cons (α := fun _ : Fin 4 => ℂ) 1 t 2 = t 1 := rfl
  have hc3 : Fin.cons (α := fun _ : Fin 4 => ℂ) 1 t 3 = t 2 := rfl
  fin_cases i <;> simp [low, mon, monExps, quadraticPairs, chart, Fin.prod_univ_succ, hc2, hc3] <;> ring

lemma quadraticEval_low (q : QuadraticIndex → ℂ) (t : Fin 3 → ℂ) :
    quadraticEval q (chart t) =
      ∑ i : Fin 10, q (quadraticEquiv i) * low t (Fin.castLE (by decide) i) := by
  rw [quadraticEval, ← Equiv.sum_comp quadraticEquiv]
  apply Finset.sum_congr rfl
  intro i hi
  rw [low_quadratic, mul_assoc]

lemma quadraticCoeffs_ne {q : QuadraticIndex → ℂ} (hq : q ≠ 0) :
    q ∘ quadraticEquiv ≠ 0 := by
  intro h
  apply hq
  ext i
  obtain ⟨j, rfl⟩ := quadraticEquiv.surjective i
  exact congrFun h j

end DimensionTen.Border

end
end

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma quadratic_zero_bound_oai (q : QuadraticIndex → ℂ) (hq : q ≠ 0) :
    (Finset.univ.filter (fun k : Fin 20 => quadraticEval q (chart (points k)) = 0)).card ≤ 9 := by
  classical
  by_contra hh
  obtain ⟨s, hs, hc⟩ := Finset.exists_subset_card_eq (show 10 ≤
    (Finset.univ.filter (fun k : Fin 20 => quadraticEval q (chart (points k)) = 0)).card by omega)
  let e : Fin 10 ≃ s := (Finset.equivFinOfCardEq hc).symm
  let b : Fin 10 → Fin 20 := fun i => e i
  have hb : Function.Injective b := Subtype.val_injective.comp e.injective
  let M : Matrix (Fin 10) (Fin 10) ℂ := fun i j => low (points (b j)) (firstTen i)
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (ten_complex_minor b hb))
  have hz : Matrix.vecMul (q ∘ quadraticEquiv) M = Matrix.vecMul 0 M := by
    rw [Matrix.zero_vecMul]
    ext j
    have hqj := (Finset.mem_filter.mp (hs (e j).property)).2
    rw [quadraticEval_low] at hqj
    exact hqj
  exact quadraticCoeffs_ne hq ((Matrix.vecMul_injective_iff_isUnit.mpr hunit) hz)

end DimensionTen.Border

end
end

end OAI
end

theorem solution : type_of% @OAI.DimensionTen.Border.quadratic_zero_bound_oai := @OAI.DimensionTen.Border.quadratic_zero_bound_oai
