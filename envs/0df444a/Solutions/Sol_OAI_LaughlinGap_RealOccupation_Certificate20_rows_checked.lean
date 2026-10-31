-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.Certificate20.rows_checked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:36:04.651984+00:00
-- url     : https://prove2.me/submissions/78b39bc8-c4e2-4aea-a928-7499ec8ddfb1

import Mathlib
import Definitions.Def_OAIQ030L028

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CachedIntegerRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cached Integer Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators

lemma exactFourEval_table (D : ℕ) (S : Fin ((D+1)/2) → Fin 8 → Fin 9 → Fin 9 → ℤ)
    (hS : ∀ u a i k, fourSumInteger a D (2*u.val+1) i k = S u a i k)
    (u v : Fin ((D+1)/2)) :
    exactFourEval D (2*u.val+1) (2*v.val+1) = integerTableEval D S u v := by
  simp only [exactFourEval,exactFourInteger,integerTableEval,hS]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CheckedTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Checked Tables. -/

noncomputable section


namespace LaughlinGap.Arithmetic

lemma checkMatrix_sound {n m : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → Fin m → α) (h : checkMatrix A B = true) : ∀ i j, A i j = B i j := by
  intro i j
  unfold checkMatrix at h
  have hh := List.all_eq_true.mp h i (List.mem_finRange i)
  exact of_decide_eq_true (List.all_eq_true.mp hh j (List.mem_finRange j))

end LaughlinGap.Arithmetic

namespace LaughlinGap.Arithmetic

lemma checkVector_sound {n : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → α) (h : checkVector A B = true) : ∀ i, A i = B i := by
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

end LaughlinGap.Arithmetic

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table20. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable20

lemma s_0_0_checked : ∀ i k : Fin 9, fourSumInteger 0 20 1 i k = s_0_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_1_checked : ∀ i k : Fin 9, fourSumInteger 1 20 1 i k = s_0_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_2_checked : ∀ i k : Fin 9, fourSumInteger 2 20 1 i k = s_0_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_3_checked : ∀ i k : Fin 9, fourSumInteger 3 20 1 i k = s_0_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_4_checked : ∀ i k : Fin 9, fourSumInteger 4 20 1 i k = s_0_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_5_checked : ∀ i k : Fin 9, fourSumInteger 5 20 1 i k = s_0_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_6_checked : ∀ i k : Fin 9, fourSumInteger 6 20 1 i k = s_0_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_7_checked : ∀ i k : Fin 9, fourSumInteger 7 20 1 i k = s_0_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_0_checked : ∀ i k : Fin 9, fourSumInteger 0 20 3 i k = s_1_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_1_checked : ∀ i k : Fin 9, fourSumInteger 1 20 3 i k = s_1_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_2_checked : ∀ i k : Fin 9, fourSumInteger 2 20 3 i k = s_1_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_3_checked : ∀ i k : Fin 9, fourSumInteger 3 20 3 i k = s_1_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_4_checked : ∀ i k : Fin 9, fourSumInteger 4 20 3 i k = s_1_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_5_checked : ∀ i k : Fin 9, fourSumInteger 5 20 3 i k = s_1_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_6_checked : ∀ i k : Fin 9, fourSumInteger 6 20 3 i k = s_1_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_7_checked : ∀ i k : Fin 9, fourSumInteger 7 20 3 i k = s_1_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_0_checked : ∀ i k : Fin 9, fourSumInteger 0 20 5 i k = s_2_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_1_checked : ∀ i k : Fin 9, fourSumInteger 1 20 5 i k = s_2_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_2_checked : ∀ i k : Fin 9, fourSumInteger 2 20 5 i k = s_2_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_3_checked : ∀ i k : Fin 9, fourSumInteger 3 20 5 i k = s_2_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_4_checked : ∀ i k : Fin 9, fourSumInteger 4 20 5 i k = s_2_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_5_checked : ∀ i k : Fin 9, fourSumInteger 5 20 5 i k = s_2_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_6_checked : ∀ i k : Fin 9, fourSumInteger 6 20 5 i k = s_2_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_7_checked : ∀ i k : Fin 9, fourSumInteger 7 20 5 i k = s_2_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_0_checked : ∀ i k : Fin 9, fourSumInteger 0 20 7 i k = s_3_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_1_checked : ∀ i k : Fin 9, fourSumInteger 1 20 7 i k = s_3_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_2_checked : ∀ i k : Fin 9, fourSumInteger 2 20 7 i k = s_3_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_3_checked : ∀ i k : Fin 9, fourSumInteger 3 20 7 i k = s_3_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_4_checked : ∀ i k : Fin 9, fourSumInteger 4 20 7 i k = s_3_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_5_checked : ∀ i k : Fin 9, fourSumInteger 5 20 7 i k = s_3_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_6_checked : ∀ i k : Fin 9, fourSumInteger 6 20 7 i k = s_3_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_7_checked : ∀ i k : Fin 9, fourSumInteger 7 20 7 i k = s_3_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_0_checked : ∀ i k : Fin 9, fourSumInteger 0 20 9 i k = s_4_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_1_checked : ∀ i k : Fin 9, fourSumInteger 1 20 9 i k = s_4_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_2_checked : ∀ i k : Fin 9, fourSumInteger 2 20 9 i k = s_4_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_3_checked : ∀ i k : Fin 9, fourSumInteger 3 20 9 i k = s_4_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_4_checked : ∀ i k : Fin 9, fourSumInteger 4 20 9 i k = s_4_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_5_checked : ∀ i k : Fin 9, fourSumInteger 5 20 9 i k = s_4_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_6_checked : ∀ i k : Fin 9, fourSumInteger 6 20 9 i k = s_4_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_7_checked : ∀ i k : Fin 9, fourSumInteger 7 20 9 i k = s_4_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_0_checked : ∀ i k : Fin 9, fourSumInteger 0 20 11 i k = s_5_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_1_checked : ∀ i k : Fin 9, fourSumInteger 1 20 11 i k = s_5_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_2_checked : ∀ i k : Fin 9, fourSumInteger 2 20 11 i k = s_5_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_3_checked : ∀ i k : Fin 9, fourSumInteger 3 20 11 i k = s_5_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_4_checked : ∀ i k : Fin 9, fourSumInteger 4 20 11 i k = s_5_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_5_checked : ∀ i k : Fin 9, fourSumInteger 5 20 11 i k = s_5_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_6_checked : ∀ i k : Fin 9, fourSumInteger 6 20 11 i k = s_5_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_7_checked : ∀ i k : Fin 9, fourSumInteger 7 20 11 i k = s_5_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_0_checked : ∀ i k : Fin 9, fourSumInteger 0 20 13 i k = s_6_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_1_checked : ∀ i k : Fin 9, fourSumInteger 1 20 13 i k = s_6_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_2_checked : ∀ i k : Fin 9, fourSumInteger 2 20 13 i k = s_6_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_3_checked : ∀ i k : Fin 9, fourSumInteger 3 20 13 i k = s_6_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_4_checked : ∀ i k : Fin 9, fourSumInteger 4 20 13 i k = s_6_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_5_checked : ∀ i k : Fin 9, fourSumInteger 5 20 13 i k = s_6_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_6_checked : ∀ i k : Fin 9, fourSumInteger 6 20 13 i k = s_6_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_7_checked : ∀ i k : Fin 9, fourSumInteger 7 20 13 i k = s_6_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_0_checked : ∀ i k : Fin 9, fourSumInteger 0 20 15 i k = s_7_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_1_checked : ∀ i k : Fin 9, fourSumInteger 1 20 15 i k = s_7_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_2_checked : ∀ i k : Fin 9, fourSumInteger 2 20 15 i k = s_7_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_3_checked : ∀ i k : Fin 9, fourSumInteger 3 20 15 i k = s_7_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_4_checked : ∀ i k : Fin 9, fourSumInteger 4 20 15 i k = s_7_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_5_checked : ∀ i k : Fin 9, fourSumInteger 5 20 15 i k = s_7_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_6_checked : ∀ i k : Fin 9, fourSumInteger 6 20 15 i k = s_7_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_7_checked : ∀ i k : Fin 9, fourSumInteger 7 20 15 i k = s_7_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_0_checked : ∀ i k : Fin 9, fourSumInteger 0 20 17 i k = s_8_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_1_checked : ∀ i k : Fin 9, fourSumInteger 1 20 17 i k = s_8_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_2_checked : ∀ i k : Fin 9, fourSumInteger 2 20 17 i k = s_8_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_3_checked : ∀ i k : Fin 9, fourSumInteger 3 20 17 i k = s_8_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_4_checked : ∀ i k : Fin 9, fourSumInteger 4 20 17 i k = s_8_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_5_checked : ∀ i k : Fin 9, fourSumInteger 5 20 17 i k = s_8_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_6_checked : ∀ i k : Fin 9, fourSumInteger 6 20 17 i k = s_8_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_7_checked : ∀ i k : Fin 9, fourSumInteger 7 20 17 i k = s_8_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_9_0_checked : ∀ i k : Fin 9, fourSumInteger 0 20 19 i k = s_9_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_9_1_checked : ∀ i k : Fin 9, fourSumInteger 1 20 19 i k = s_9_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_9_2_checked : ∀ i k : Fin 9, fourSumInteger 2 20 19 i k = s_9_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_9_3_checked : ∀ i k : Fin 9, fourSumInteger 3 20 19 i k = s_9_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_9_4_checked : ∀ i k : Fin 9, fourSumInteger 4 20 19 i k = s_9_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_9_5_checked : ∀ i k : Fin 9, fourSumInteger 5 20 19 i k = s_9_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_9_6_checked : ∀ i k : Fin 9, fourSumInteger 6 20 19 i k = s_9_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_9_7_checked : ∀ i k : Fin 9, fourSumInteger 7 20 19 i k = s_9_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma sums_checked : ∀ u : Fin 10, ∀ a i k, fourSumInteger a 20 (2*u.val+1) i k = sums u a i k := by
  intro u a i k
  fin_cases u <;> fin_cases a
  · exact s_0_0_checked i k
  · exact s_0_1_checked i k
  · exact s_0_2_checked i k
  · exact s_0_3_checked i k
  · exact s_0_4_checked i k
  · exact s_0_5_checked i k
  · exact s_0_6_checked i k
  · exact s_0_7_checked i k
  · exact s_1_0_checked i k
  · exact s_1_1_checked i k
  · exact s_1_2_checked i k
  · exact s_1_3_checked i k
  · exact s_1_4_checked i k
  · exact s_1_5_checked i k
  · exact s_1_6_checked i k
  · exact s_1_7_checked i k
  · exact s_2_0_checked i k
  · exact s_2_1_checked i k
  · exact s_2_2_checked i k
  · exact s_2_3_checked i k
  · exact s_2_4_checked i k
  · exact s_2_5_checked i k
  · exact s_2_6_checked i k
  · exact s_2_7_checked i k
  · exact s_3_0_checked i k
  · exact s_3_1_checked i k
  · exact s_3_2_checked i k
  · exact s_3_3_checked i k
  · exact s_3_4_checked i k
  · exact s_3_5_checked i k
  · exact s_3_6_checked i k
  · exact s_3_7_checked i k
  · exact s_4_0_checked i k
  · exact s_4_1_checked i k
  · exact s_4_2_checked i k
  · exact s_4_3_checked i k
  · exact s_4_4_checked i k
  · exact s_4_5_checked i k
  · exact s_4_6_checked i k
  · exact s_4_7_checked i k
  · exact s_5_0_checked i k
  · exact s_5_1_checked i k
  · exact s_5_2_checked i k
  · exact s_5_3_checked i k
  · exact s_5_4_checked i k
  · exact s_5_5_checked i k
  · exact s_5_6_checked i k
  · exact s_5_7_checked i k
  · exact s_6_0_checked i k
  · exact s_6_1_checked i k
  · exact s_6_2_checked i k
  · exact s_6_3_checked i k
  · exact s_6_4_checked i k
  · exact s_6_5_checked i k
  · exact s_6_6_checked i k
  · exact s_6_7_checked i k
  · exact s_7_0_checked i k
  · exact s_7_1_checked i k
  · exact s_7_2_checked i k
  · exact s_7_3_checked i k
  · exact s_7_4_checked i k
  · exact s_7_5_checked i k
  · exact s_7_6_checked i k
  · exact s_7_7_checked i k
  · exact s_8_0_checked i k
  · exact s_8_1_checked i k
  · exact s_8_2_checked i k
  · exact s_8_3_checked i k
  · exact s_8_4_checked i k
  · exact s_8_5_checked i k
  · exact s_8_6_checked i k
  · exact s_8_7_checked i k
  · exact s_9_0_checked i k
  · exact s_9_1_checked i k
  · exact s_9_2_checked i k
  · exact s_9_3_checked i k
  · exact s_9_4_checked i k
  · exact s_9_5_checked i k
  · exact s_9_6_checked i k
  · exact s_9_7_checked i k
end SumTable20
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate20

lemma rows_table_checked_0 : ∀ v : Fin 10, integerTableEval 20 SumTable20.sums (0 : Fin 10) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 10, integerTableEval 20 SumTable20.sums (1 : Fin 10) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 10, integerTableEval 20 SumTable20.sums (2 : Fin 10) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_3 : ∀ v : Fin 10, integerTableEval 20 SumTable20.sums (3 : Fin 10) v = Y 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_4 : ∀ v : Fin 10, integerTableEval 20 SumTable20.sums (4 : Fin 10) v = Y 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_5 : ∀ v : Fin 10, integerTableEval 20 SumTable20.sums (5 : Fin 10) v = Y 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_6 : ∀ v : Fin 10, integerTableEval 20 SumTable20.sums (6 : Fin 10) v = Y 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_7 : ∀ v : Fin 10, integerTableEval 20 SumTable20.sums (7 : Fin 10) v = Y 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_8 : ∀ v : Fin 10, integerTableEval 20 SumTable20.sums (8 : Fin 10) v = Y 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_9 : ∀ v : Fin 10, integerTableEval 20 SumTable20.sums (9 : Fin 10) v = Y 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 10, ∀ v : Fin 10, integerTableEval 20 SumTable20.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
  · exact rows_table_checked_3
  · exact rows_table_checked_4
  · exact rows_table_checked_5
  · exact rows_table_checked_6
  · exact rows_table_checked_7
  · exact rows_table_checked_8
  · exact rows_table_checked_9
lemma rows_checked_oai (u v : Fin 10) : exactFourEval 20 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 20 SumTable20.sums SumTable20.sums_checked]
  exact rows_table_checked u v
end Certificate20
end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.Certificate20.rows_checked_oai := @OAI.LaughlinGap.RealOccupation.Certificate20.rows_checked_oai
