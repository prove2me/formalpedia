-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_9_s50
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:54:46.116496+00:00
-- url     : https://prove2.me/submissions/ee8bacae-2413-495a-9903-bb5a4ebac2ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_9_9_9_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeRow09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_9_1_3_0 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[0]!) =
    (-279062421380172067529857348024358190744997899746987212800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_1 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[1]!) =
    (-459360885322437236466125812039608637656853533960437760000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_2 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[2]!) =
    (216813933383140622295232522828123519722286834934140108800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_3 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[3]!) =
    (14938515937034594999877003710229050926038061338014515200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_4 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[4]!) =
    (-24008230324336158937040680586644171361887125491417088000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_5 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[5]!) =
    (109393309605793398426247870349258171849606499573694464000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_6 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[6]!) =
    (8721086357081805385975272257328250909745983137408614400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_0 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[0]!) =
    (14787836285160721543724787969959397141990595790635008000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_1 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[1]!) =
    (336320165288866155966027442267636959269808379338424320000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_2 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[2]!) =
    (9732573989302727334672116253191299087851537214262476800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_3 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[3]!) =
    (33886163539748383224392155439022704107458560405589196800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_4 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[4]!) =
    (16923800992130264548028553653580871266607186616883609600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_5 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[5]!) =
    (46576080143532248793028769123169977841188974384014950400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_6 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[6]!) =
    (-7806328388432177408073340623748203428941925474893824000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeRow092
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_9_3_5_0 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[0]!) =
    (8943603016536055842852973607432799785981824725732556800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_5_1 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[1]!) =
    (-251721159274289624971784653147597378347202310528040960000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_5_2 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[2]!) =
    (30856573776962976395503016709439403238848723287434854400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_5_3 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[3]!) =
    (-45428231968076840608089889236946961965552350438988185600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_5_4 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[4]!) =
    (1840739597139051079457637812474924906987764596709785600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_5_5 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[5]!) =
    (28364736260211343827393001222742840528698889371385856000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_5_6 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[6]!) =
    (-46346496825727039607863683025836935535518947265740800000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeRow093
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_9_5_7_0 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[0]!) =
    (37484588852647132890760534582881181405001812758704947200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_7_1 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[1]!) =
    (-511362978859533248104163501739314364391697144988303360000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_7_2 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[2]!) =
    (-138626485543771537044192482926094436237431707100459827200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_7_3 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[3]!) =
    (50932529603893774815823364097813077314064220530776473600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_7_4 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[4]!) =
    (1152950035722211064982468230212159927150714408874803200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_7_5 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[5]!) =
    (-20888681307310678226735427883924546231730943832778342400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_7_6 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[6]!) =
    (1266592853361175696920124646706138230670133092050534400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_0 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[0]!) =
    (1730299036951487279704336142420470070729823124691563315200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_1 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[1]!) =
    (-302627006093845813559800606047016673864445229919109120000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_2 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[2]!) =
    (309277799821075773840357757352339316425496796134899712000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_3 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[3]!) =
    (48023594568254777314005298943874196381302147438870528000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_4 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[4]!) =
    (-14171658115507171948684957793767797136158427254777446400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_5 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[5]!) =
    (84700007125431340587265300729828955859716934862268006400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_6 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[6]!) =
    (-16443967375424498629864692499661996754210893446565068800000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RowBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_yRow_eq_rowCompute (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (RowCompute.yRowIntegralFast D r s (RowCompute.rows[n]!) : ℚ) / arithmeticScale := by
  exact source_yRow_eq_fastIntegral D r s n hn

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_9_1_3 : Y 9 1 3 = (-33961811903853786055197/838860800000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 3 0 (by decide),
    source_yRow_eq_rowCompute 9 1 3 1 (by decide),
    source_yRow_eq_rowCompute 9 1 3 2 (by decide),
    source_yRow_eq_rowCompute 9 1 3 3 (by decide),
    source_yRow_eq_rowCompute 9 1 3 4 (by decide),
    source_yRow_eq_rowCompute 9 1 3 5 (by decide),
    source_yRow_eq_rowCompute 9 1 3 6 (by decide),
    computeRow_9_1_3_0, computeRow_9_1_3_1, computeRow_9_1_3_2, computeRow_9_1_3_3, computeRow_9_1_3_4, computeRow_9_1_3_5, computeRow_9_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_1_5 : Y 9 1 5 = (-670994343426034247927913/6710886400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 5 0 (by decide),
    source_yRow_eq_rowCompute 9 1 5 1 (by decide),
    source_yRow_eq_rowCompute 9 1 5 2 (by decide),
    source_yRow_eq_rowCompute 9 1 5 3 (by decide),
    source_yRow_eq_rowCompute 9 1 5 4 (by decide),
    source_yRow_eq_rowCompute 9 1 5 5 (by decide),
    source_yRow_eq_rowCompute 9 1 5 6 (by decide),
    computeRow_9_1_5_0, computeRow_9_1_5_1, computeRow_9_1_5_2, computeRow_9_1_5_3, computeRow_9_1_5_4, computeRow_9_1_5_5, computeRow_9_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_3_5 : Y 9 3 5 = (-249132079557021880785303/11744051200000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 3 5 0 (by decide),
    source_yRow_eq_rowCompute 9 3 5 1 (by decide),
    source_yRow_eq_rowCompute 9 3 5 2 (by decide),
    source_yRow_eq_rowCompute 9 3 5 3 (by decide),
    source_yRow_eq_rowCompute 9 3 5 4 (by decide),
    source_yRow_eq_rowCompute 9 3 5 5 (by decide),
    source_yRow_eq_rowCompute 9 3 5 6 (by decide),
    computeRow_9_3_5_0, computeRow_9_3_5_1, computeRow_9_3_5_2, computeRow_9_3_5_3, computeRow_9_3_5_4, computeRow_9_3_5_5, computeRow_9_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_5_7 : Y 9 5 7 = (202846259663372040293217/3355443200000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 5 7 0 (by decide),
    source_yRow_eq_rowCompute 9 5 7 1 (by decide),
    source_yRow_eq_rowCompute 9 5 7 2 (by decide),
    source_yRow_eq_rowCompute 9 5 7 3 (by decide),
    source_yRow_eq_rowCompute 9 5 7 4 (by decide),
    source_yRow_eq_rowCompute 9 5 7 5 (by decide),
    source_yRow_eq_rowCompute 9 5 7 6 (by decide),
    computeRow_9_5_7_0, computeRow_9_5_7_1, computeRow_9_5_7_2, computeRow_9_5_7_3, computeRow_9_5_7_4, computeRow_9_5_7_5, computeRow_9_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_7_7 : Y 9 7 7 = (-3138981013037239731556773/1677721600000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 7 7 0 (by decide),
    source_yRow_eq_rowCompute 9 7 7 1 (by decide),
    source_yRow_eq_rowCompute 9 7 7 2 (by decide),
    source_yRow_eq_rowCompute 9 7 7 3 (by decide),
    source_yRow_eq_rowCompute 9 7 7 4 (by decide),
    source_yRow_eq_rowCompute 9 7 7 5 (by decide),
    source_yRow_eq_rowCompute 9 7 7 6 (by decide),
    computeRow_9_7_7_0, computeRow_9_7_7_1, computeRow_9_7_7_2, computeRow_9_7_7_3, computeRow_9_7_7_4, computeRow_9_7_7_5, computeRow_9_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem error_9_s50_oai : errorRational 9 = candidateY_9 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_9_1_1_s50
  · exact source_error_9_1_3
  · exact source_error_9_1_5
  · exact source_error_9_1_7_s50
  · exact source_error_9_1_9_s50
  · exact source_error_9_3_1_s50
  · exact source_error_9_3_3_s50
  · exact source_error_9_3_5
  · exact source_error_9_3_7_s50
  · exact source_error_9_3_9_s50
  · exact source_error_9_5_1_s50
  · exact source_error_9_5_3_s50
  · exact source_error_9_5_5_s50
  · exact source_error_9_5_7
  · exact source_error_9_5_9_s50
  · exact source_error_9_7_1_s50
  · exact source_error_9_7_3_s50
  · exact source_error_9_7_5_s50
  · exact source_error_9_7_7
  · exact source_error_9_7_9_s50
  · exact source_error_9_9_1_s50
  · exact source_error_9_9_3_s50
  · exact source_error_9_9_5_s50
  · exact source_error_9_9_7_s50
  · exact source_error_9_9_9_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.error_9_s50_oai := @OAI.Laughlin.Certificate.error_9_s50_oai
