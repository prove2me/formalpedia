-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_8_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:50:47.200046+00:00
-- url     : https://prove2.me/submissions/0c00b1f1-8e7a-4f28-8e89-97b0df0c7dd5

import Mathlib
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_7_7_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators Matrix

theorem Y_expand (D r s : ℕ) : Y D r s =
    -(yRow D r s (rows[0]!) + (yRow D r s (rows[1]!) +
      (yRow D r s (rows[2]!) + (yRow D r s (rows[3]!) +
        (yRow D r s (rows[4]!) + (yRow D r s (rows[5]!) +
          (yRow D r s (rows[6]!) + 0))))))) / (10^14 : ℚ) := by rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Integral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_eq_integral (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (ht : t ≤ 16) (hT : e.1 + e.2.1 + (f.1 + f.2.1 - t) ≤ 24) :
    yEntry D r s t e f = (yEntryIntegral D r s t e f : ℚ) / arithmeticScale := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp at hT
  let T := p+j+(q+l-t)
  let z : ℤ := 1-2*((p : ℤ)+(j : ℤ)+(q+l-t : ℕ))+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r : ℤ)+(s : ℤ))/2
  have hz : 0 ≤ 64+z := by dsimp [z,T]; omega
  have hexp : 65-2*((p : ℤ)+(j : ℤ)+(q+l-t : ℕ))+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r : ℤ)+(s : ℤ))/2 = 64+z := by dsimp [z]; ring
  have hp : (2 : ℚ)^((64+z).toNat) = (2 : ℚ)^64 * (2 : ℚ)^z := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hz, zpow_add₀ (by norm_num)]
    norm_num
  have hTD : T-D ≤ 24 := by dsimp [T]; omega
  have hf : ((T-D).factorial : ℚ) * ((24 : ℕ).descFactorial (24-(T-D)) : ℚ) = (Nat.factorial 24 : ℚ) := by
    have hn := Nat.factorial_mul_descFactorial (n := 24) (k := 24-(T-D)) (by omega)
    rw [Nat.sub_sub_self hTD] at hn
    exact_mod_cast hn
  dsimp [yEntry, yEntryIntegral]
  split_ifs with hd
  · change _ = _ / arithmeticScale
    rw [hexp]
    push_cast
    rw [hp]
    change _ = _ / ((2 : ℚ)^64 * (Nat.factorial 24 : ℚ))
    rw [← hf]
    have hn : ((T-D).factorial : ℚ) ≠ 0 := by positivity
    have hm : ((24 : ℕ).descFactorial (24-(T-D)) : ℚ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hf
      exact (ne_of_gt (show (0 : ℚ) < (Nat.factorial 24 : ℚ) by positivity)) hf.symm
    change _ = _ / ((2 : ℚ)^64 * (((T-D).factorial : ℚ) * ((24 : ℕ).descFactorial (24-(T-D)) : ℚ)))
    field_simp
    ring
  · simp

private theorem sum_integral {Element : Type*} (xs : List Element) (f : Element → ℤ) (c : ℚ) :
    (xs.map (fun x => (f x : ℚ)/c)).sum = ((xs.map f).sum : ℚ)/c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_div]

theorem yRow_eq_integral (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (ht : row.1 ≤ 16)
    (hT : ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24) :
    yRow D r s row = (yRowIntegral D r s row : ℚ) / arithmeticScale := by
  unfold yRow yRowIntegral
  calc
    _ = (row.2.2.map (fun e => (row.2.2.map (fun f =>
        (yEntryIntegral D r s row.1 e f : ℚ)/arithmeticScale)).sum)).sum := by
      congr 1
      apply List.map_congr_left
      intro e he
      congr 1
      apply List.map_congr_left
      intro f hf
      exact yEntry_eq_integral D r s row.1 e f ht (hT e he f hf)
    _ = _ := by simp_rw [sum_integral]

theorem rows_integral_bounds : ∀ row ∈ rows, row.1 ≤ 16 ∧
    ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24 := by
  decide +kernel

theorem source_yRow_eq_integral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegral D r s (rows[n]!) : ℚ) / arithmeticScale := by
  have hm : rows[n]! ∈ rows := by
    interval_cases n <;> decide +kernel
  exact yRow_eq_integral D r s _ (rows_integral_bounds _ hm).1 (rows_integral_bounds _ hm).2

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Row08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_8_1_1_0 : yRow 8 1 1 (rows[0]!) = (-1542335899954614345/2048 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 1 0 (by decide)]
  have h : yRowIntegral 8 1 1 (rows[0]!) = (-8619347850272953673098966182318281602089400786118246400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_1_1 : yRow 8 1 1 (rows[1]!) = (-75316015709295173739/8388608 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 1 1 (by decide)]
  have h : yRowIntegral 8 1 1 (rows[1]!) = (-102759700481278136454049635014896858919534980057006080000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_1_2 : yRow 8 1 1 (rows[2]!) = (-9136760184633772519965/33554432 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 1 2 (by decide)]
  have h : yRowIntegral 8 1 1 (rows[2]!) = (-3116504275684753840824333987016605727399506032669491200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_1_3 : yRow 8 1 1 (rows[3]!) = (526208461257856971342675/67108864 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 1 3 (by decide)]
  have h : yRowIntegral 8 1 1 (rows[3]!) = (89743568084978664405363388204529436242875518101225472000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_1_4 : yRow 8 1 1 (rows[4]!) = (14597567158110194070375/16777216 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 1 4 (by decide)]
  have h : yRowIntegral 8 1 1 (rows[4]!) = (9958317728281114061683907653004378575256490564648960000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_1_5 : yRow 8 1 1 (rows[5]!) = (-347441421785295611479515/67108864 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 1 5 (by decide)]
  have h : yRowIntegral 8 1 1 (rows[5]!) = (-59255286045754170219483300870860577850712898244549017600000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_1_6 : yRow 8 1 1 (rows[6]!) = (-8205115144686782088375/16777216 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 1 6 (by decide)]
  have h : yRowIntegral 8 1 1 (rows[6]!) = (-5597449405295309043794642493309726317975774366269440000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_3_0 : yRow 8 1 3 (rows[0]!) = (-11387494346113586295/8192 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 3 0 (by decide)]
  have h : yRowIntegral 8 1 3 (rows[0]!) = (-15909759818703865639420918948060704312505350737205657600000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_3_1 : yRow 8 1 3 (rows[1]!) = (197119650262423977/524288 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 3 1 (by decide)]
  have h : yRowIntegral 8 1 3 (rows[1]!) = (4303139199104731278274793995541665105689055372247040000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_3_2 : yRow 8 1 3 (rows[2]!) = (36872577681837689686995/16777216 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 3 2 (by decide)]
  have h : yRowIntegral 8 1 3 (rows[2]!) = (25154112328400015358321224590538739271019887395550003200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_3_3 : yRow 8 1 3 (rows[3]!) = (15064379418747419024745/33554432 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 3 3 (by decide)]
  have h : yRowIntegral 8 1 3 (rows[3]!) = (5138386246365681146408405211272447483086217886144921600000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_3_4 : yRow 8 1 3 (rows[4]!) = (-441299603451117593115/33554432 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 3 4 (by decide)]
  have h : yRowIntegral 8 1 3 (rows[4]!) = (-150525139460965372092090500551256731669027559256883200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_3_5 : yRow 8 1 3 (rows[5]!) = (-6630239381949782627055/16777216 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 3 5 (by decide)]
  have h : yRowIntegral 8 1 3 (rows[5]!) = (-4523084543120943521189449142964840775985106302848204800000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_3_6 : yRow 8 1 3 (rows[6]!) = (-397903947246140783805/4194304 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 3 6 (by decide)]
  have h : yRowIntegral 8 1 3 (rows[6]!) = (-1085784744566232926682825961496439763504947159839539200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_5_0 : yRow 8 1 5 (rows[0]!) = (-14645438327407983795/2048 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 5 0 (by decide)]
  have h : yRowIntegral 8 1 5 (rows[0]!) = (-81846066973714198535257051527707951684592003606537830400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_5_1 : yRow 8 1 5 (rows[1]!) = (-18171099948981591081/2097152 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 5 1 (by decide)]
  have h : yRowIntegral 8 1 5 (rows[1]!) = (-99169175139585513026729613548820931756850687539937280000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_5_2 : yRow 8 1 5 (rows[2]!) = (-35901747833688299761245/8388608 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 5 2 (by decide)]
  have h : yRowIntegral 8 1 5 (rows[2]!) = (-48983643377843663525738690465967873761696349774308966400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_5_3 : yRow 8 1 5 (rows[3]!) = (13068275739016009424895/16777216 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 5 3 (by decide)]
  have h : yRowIntegral 8 1 5 (rows[3]!) = (8915050060078423264496009358264607986567716386583347200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_5_4 : yRow 8 1 5 (rows[4]!) = (-102541802088869818905/2097152 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 5 4 (by decide)]
  have h : yRowIntegral 8 1 5 (rows[4]!) = (-559624126169080528107859221332441491696940415870566400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_5_5 : yRow 8 1 5 (rows[5]!) = (-142185036639416818007445/67108864 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 5 5 (by decide)]
  have h : yRowIntegral 8 1 5 (rows[5]!) = (-24249310787995549471600525782497902890479770894388428800000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_5_6 : yRow 8 1 5 (rows[6]!) = (-177811778631486817125/8388608 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 5 6 (by decide)]
  have h : yRowIntegral 8 1 5 (rows[6]!) = (-242602917083940767689579220014547693785978062766080000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_FastChoose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem U_eq_fast (c z T p : ℕ) : U c z T p = UFast c z T p := by
  simp only [U, UFast, Nat.choose_eq_fast_choose]

theorem V_eq_fast (r D T p j k : ℕ) : V r D T p j k = VFast r D T p j k := by
  simp only [V, VFast, U_eq_fast]

theorem yEntryIntegral_eq_fast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    yEntryIntegral D r s t e f = yEntryIntegralFast D r s t e f := by
  simp only [yEntryIntegral, yEntryIntegralFast, V_eq_fast]

theorem yRowIntegral_eq_fast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    yRowIntegral D r s row = yRowIntegralFast D r s row := by
  simp only [yRowIntegral, yRowIntegralFast, yEntryIntegral_eq_fast]

theorem source_yRow_eq_fastIntegral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegralFast D r s (rows[n]!) : ℚ) / arithmeticScale := by
  rw [source_yRow_eq_integral D r s n hn, yRowIntegral_eq_fast]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Row082
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_8_3_3_0 : yRow 8 3 3 (rows[0]!) = (15977720834090203455/8192 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 3 0 (by decide)]
  have h : yRowIntegralFast 8 3 3 (rows[0]!) = (22322882733850216101237666734600677605481762670405222400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_3_1 : yRow 8 3 3 (rows[1]!) = (3142036540605854661/2097152 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 3 1 (by decide)]
  have h : yRowIntegralFast 8 3 3 (rows[1]!) = (17147733096244555833634088409268874847094058967367680000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_3_2 : yRow 8 3 3 (rows[2]!) = (685667686484171871195/8388608 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 3 2 (by decide)]
  have h : yRowIntegralFast 8 3 3 (rows[2]!) = (935511596428071271256193942280031406802407155721830400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_3_3 : yRow 8 3 3 (rows[3]!) = (-18744793144766932510845/16777216 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 3 3 (by decide)]
  have h : yRowIntegralFast 8 3 3 (rows[3]!) = (-12787514786858549425344796377195048608240794860729139200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_3_4 : yRow 8 3 3 (rows[4]!) = (-6097593366856360539375/234881024 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 3 4 (by decide)]
  have h : yRowIntegralFast 8 3 3 (rows[4]!) = (-297122759602537588518861771098439094257983894323200000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_3_5 : yRow 8 3 3 (rows[5]!) = (32391427003169138594775/234881024 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 3 5 (by decide)]
  have h : yRowIntegralFast 8 3 3 (rows[5]!) = (1578365364761537085254234510698954482866065816682496000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_3_6 : yRow 8 3 3 (rows[6]!) = (-1988696899266245149545/33554432 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 3 6 (by decide)]
  have h : yRowIntegralFast 8 3 3 (rows[6]!) = (-678334799683996527711351806702633338084636298418585600000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_5_0 : yRow 8 3 5 (rows[0]!) = (76640875416000675/1024 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 5 0 (by decide)]
  have h : yRowIntegralFast 8 3 5 (rows[0]!) = (856615429595306325025256914923187604516818661670912000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_5_1 : yRow 8 3 5 (rows[1]!) = (174426263694933807/524288 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 5 1 (by decide)]
  have h : yRowIntegralFast 8 3 5 (rows[1]!) = (3807740586287595884710452381718919859920364518768640000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_5_2 : yRow 8 3 5 (rows[2]!) = (2761275840379361416995/4194304 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 5 2 (by decide)]
  have h : yRowIntegralFast 8 3 5 (rows[2]!) = (7534861626211962036591583876263875363608284577451212800000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_5_3 : yRow 8 3 5 (rows[3]!) = (702428309218164239085/8388608 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 5 3 (by decide)]
  have h : yRowIntegralFast 8 3 5 (rows[3]!) = (958379462655522227776546507336903612321559804588851200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_5_4 : yRow 8 3 5 (rows[4]!) = (2911950561638159921355/33554432 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 5 4 (by decide)]
  have h : yRowIntegralFast 8 3 5 (rows[4]!) = (993252114813135149443158640425212610753801639847526400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_5_5 : yRow 8 3 5 (rows[5]!) = (20424443618431088962035/58720256 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 5 5 (by decide)]
  have h : yRowIntegralFast 8 3 5 (rows[5]!) = (3980958838115082923031199520266531892326567020960153600000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_5_6 : yRow 8 3 5 (rows[6]!) = (-74303915387983228845/2097152 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 5 6 (by decide)]
  have h : yRowIntegralFast 8 3 5 (rows[6]!) = (-405515242299948507369798187993398981045996312172953600000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_0 : yRow 8 3 7 (rows[0]!) = (1990312643635120665/2048 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 0 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[0]!) = (11122866949276273240494885445024757470322608040627404800000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_1 : yRow 8 3 7 (rows[1]!) = (-1095344391635191101/524288 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 1 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[1]!) = (-23911463833717104904155617528637173818730653176299520000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_2 : yRow 8 3 7 (rows[2]!) = (11311749600528369600555/2097152 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 2 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[2]!) = (61734120687218218053787138616255934133213958544713318400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_3 : yRow 8 3 7 (rows[3]!) = (8603647500660654488295/4194304 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 3 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[3]!) = (23477297142930871074039406428360714858159574168161484800000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_4 : yRow 8 3 7 (rows[4]!) = (3519874183592373572895/16777216 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 4 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[4]!) = (2401223786411049713220922466624398209967081271800627200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_5 : yRow 8 3 7 (rows[5]!) = (-3479431231969799395785/8388608 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 5 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[5]!) = (-4747267999710378909098188438704975869751880355885875200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_6 : yRow 8 3 7 (rows[6]!) = (672523966016989221555/4194304 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 6 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[6]!) = (1835157121989341670710322442697238660354473731502899200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Error08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem error_8_1_1 : Y 8 1 1 = (-67460768130800149252179/3355443200000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_1_0, yRow_8_1_1_1, yRow_8_1_1_2, yRow_8_1_1_3, yRow_8_1_1_4, yRow_8_1_1_5, yRow_8_1_1_6]
  norm_num

theorem error_8_1_3 : Y 8 1 3 = (-12646981826519267475639/1677721600000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_3_0, yRow_8_1_3_1, yRow_8_1_3_2, yRow_8_1_3_3, yRow_8_1_3_4, yRow_8_1_3_5, yRow_8_1_3_6]
  norm_num

theorem error_8_1_5 : Y 8 1 5 = (862312946559627131048937/6710886400000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_5_0, yRow_8_1_5_1, yRow_8_1_5_2, yRow_8_1_5_3, yRow_8_1_5_4, yRow_8_1_5_5, yRow_8_1_5_6]
  norm_num

theorem error_8_3_3 : Y 8 3 3 = (-227609666383850988434007/23488102400000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_3_3_0, yRow_8_3_3_1, yRow_8_3_3_2, yRow_8_3_3_3, yRow_8_3_3_4, yRow_8_3_3_5, yRow_8_3_3_6]
  norm_num

theorem error_8_3_5 : Y 8 3 5 = (-285716550006646092887421/23488102400000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_3_5_0, yRow_8_3_5_1, yRow_8_3_5_2, yRow_8_3_5_3, yRow_8_3_5_4, yRow_8_3_5_5, yRow_8_3_5_6]
  norm_num

theorem error_8_3_7 : Y 8 3 7 = (-140429284546716888797613/1677721600000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_3_7_0, yRow_8_3_7_1, yRow_8_3_7_2, yRow_8_3_7_3, yRow_8_3_7_4, yRow_8_3_7_5, yRow_8_3_7_6]
  norm_num

theorem error_8_s50_oai : errorRational 8 =
    !![-67460768130800149252179/3355443200000000000000, -12646981826519267475639/1677721600000000000000, 862312946559627131048937/6710886400000000000000, 145152021796677708235047/3355443200000000000000;
      -12646981826519267475639/1677721600000000000000, -227609666383850988434007/23488102400000000000000, -285716550006646092887421/23488102400000000000000, -140429284546716888797613/1677721600000000000000;
      862312946559627131048937/6710886400000000000000, -285716550006646092887421/23488102400000000000000, 1048952949137524188240279/46976204800000000000000, 707573349496458024998847/3355443200000000000000;
      145152021796677708235047/3355443200000000000000, -140429284546716888797613/1677721600000000000000, 707573349496458024998847/3355443200000000000000, -2475302483264003426615343/1677721600000000000000] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact error_8_1_1
  · exact error_8_1_3
  · exact error_8_1_5
  · exact error_8_1_7_s50
  · exact error_8_3_1_s50
  · exact error_8_3_3
  · exact error_8_3_5
  · exact error_8_3_7
  · exact error_8_5_1_s50
  · exact error_8_5_3_s50
  · exact error_8_5_5_s50
  · exact error_8_5_7_s50
  · exact error_8_7_1_s50
  · exact error_8_7_3_s50
  · exact error_8_7_5_s50
  · exact error_8_7_7_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.error_8_s50_oai := @OAI.Laughlin.Certificate.error_8_s50_oai
