-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.Certificate17.rows_checked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:29:30.814979+00:00
-- url     : https://prove2.me/submissions/c6c7bec3-e468-48ea-85b1-4080fab7cb47

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
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table17. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable17

lemma s_0_0_checked : ∀ i k : Fin 9, fourSumInteger 0 17 1 i k = s_0_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_1_checked : ∀ i k : Fin 9, fourSumInteger 1 17 1 i k = s_0_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_2_checked : ∀ i k : Fin 9, fourSumInteger 2 17 1 i k = s_0_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_3_checked : ∀ i k : Fin 9, fourSumInteger 3 17 1 i k = s_0_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_4_checked : ∀ i k : Fin 9, fourSumInteger 4 17 1 i k = s_0_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_5_checked : ∀ i k : Fin 9, fourSumInteger 5 17 1 i k = s_0_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_6_checked : ∀ i k : Fin 9, fourSumInteger 6 17 1 i k = s_0_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_7_checked : ∀ i k : Fin 9, fourSumInteger 7 17 1 i k = s_0_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_0_checked : ∀ i k : Fin 9, fourSumInteger 0 17 3 i k = s_1_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_1_checked : ∀ i k : Fin 9, fourSumInteger 1 17 3 i k = s_1_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_2_checked : ∀ i k : Fin 9, fourSumInteger 2 17 3 i k = s_1_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_3_checked : ∀ i k : Fin 9, fourSumInteger 3 17 3 i k = s_1_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_4_checked : ∀ i k : Fin 9, fourSumInteger 4 17 3 i k = s_1_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_5_checked : ∀ i k : Fin 9, fourSumInteger 5 17 3 i k = s_1_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_6_checked : ∀ i k : Fin 9, fourSumInteger 6 17 3 i k = s_1_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_7_checked : ∀ i k : Fin 9, fourSumInteger 7 17 3 i k = s_1_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_0_checked : ∀ i k : Fin 9, fourSumInteger 0 17 5 i k = s_2_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_1_checked : ∀ i k : Fin 9, fourSumInteger 1 17 5 i k = s_2_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_2_checked : ∀ i k : Fin 9, fourSumInteger 2 17 5 i k = s_2_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_3_checked : ∀ i k : Fin 9, fourSumInteger 3 17 5 i k = s_2_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_4_checked : ∀ i k : Fin 9, fourSumInteger 4 17 5 i k = s_2_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_5_checked : ∀ i k : Fin 9, fourSumInteger 5 17 5 i k = s_2_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_6_checked : ∀ i k : Fin 9, fourSumInteger 6 17 5 i k = s_2_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_7_checked : ∀ i k : Fin 9, fourSumInteger 7 17 5 i k = s_2_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_0_checked : ∀ i k : Fin 9, fourSumInteger 0 17 7 i k = s_3_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_1_checked : ∀ i k : Fin 9, fourSumInteger 1 17 7 i k = s_3_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_2_checked : ∀ i k : Fin 9, fourSumInteger 2 17 7 i k = s_3_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_3_checked : ∀ i k : Fin 9, fourSumInteger 3 17 7 i k = s_3_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_4_checked : ∀ i k : Fin 9, fourSumInteger 4 17 7 i k = s_3_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_5_checked : ∀ i k : Fin 9, fourSumInteger 5 17 7 i k = s_3_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_6_checked : ∀ i k : Fin 9, fourSumInteger 6 17 7 i k = s_3_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_3_7_checked : ∀ i k : Fin 9, fourSumInteger 7 17 7 i k = s_3_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_0_checked : ∀ i k : Fin 9, fourSumInteger 0 17 9 i k = s_4_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_1_checked : ∀ i k : Fin 9, fourSumInteger 1 17 9 i k = s_4_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_2_checked : ∀ i k : Fin 9, fourSumInteger 2 17 9 i k = s_4_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_3_checked : ∀ i k : Fin 9, fourSumInteger 3 17 9 i k = s_4_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_4_checked : ∀ i k : Fin 9, fourSumInteger 4 17 9 i k = s_4_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_5_checked : ∀ i k : Fin 9, fourSumInteger 5 17 9 i k = s_4_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_6_checked : ∀ i k : Fin 9, fourSumInteger 6 17 9 i k = s_4_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_4_7_checked : ∀ i k : Fin 9, fourSumInteger 7 17 9 i k = s_4_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_0_checked : ∀ i k : Fin 9, fourSumInteger 0 17 11 i k = s_5_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_1_checked : ∀ i k : Fin 9, fourSumInteger 1 17 11 i k = s_5_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_2_checked : ∀ i k : Fin 9, fourSumInteger 2 17 11 i k = s_5_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_3_checked : ∀ i k : Fin 9, fourSumInteger 3 17 11 i k = s_5_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_4_checked : ∀ i k : Fin 9, fourSumInteger 4 17 11 i k = s_5_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_5_checked : ∀ i k : Fin 9, fourSumInteger 5 17 11 i k = s_5_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_6_checked : ∀ i k : Fin 9, fourSumInteger 6 17 11 i k = s_5_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_5_7_checked : ∀ i k : Fin 9, fourSumInteger 7 17 11 i k = s_5_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_0_checked : ∀ i k : Fin 9, fourSumInteger 0 17 13 i k = s_6_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_1_checked : ∀ i k : Fin 9, fourSumInteger 1 17 13 i k = s_6_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_2_checked : ∀ i k : Fin 9, fourSumInteger 2 17 13 i k = s_6_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_3_checked : ∀ i k : Fin 9, fourSumInteger 3 17 13 i k = s_6_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_4_checked : ∀ i k : Fin 9, fourSumInteger 4 17 13 i k = s_6_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_5_checked : ∀ i k : Fin 9, fourSumInteger 5 17 13 i k = s_6_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_6_checked : ∀ i k : Fin 9, fourSumInteger 6 17 13 i k = s_6_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_6_7_checked : ∀ i k : Fin 9, fourSumInteger 7 17 13 i k = s_6_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_0_checked : ∀ i k : Fin 9, fourSumInteger 0 17 15 i k = s_7_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_1_checked : ∀ i k : Fin 9, fourSumInteger 1 17 15 i k = s_7_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_2_checked : ∀ i k : Fin 9, fourSumInteger 2 17 15 i k = s_7_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_3_checked : ∀ i k : Fin 9, fourSumInteger 3 17 15 i k = s_7_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_4_checked : ∀ i k : Fin 9, fourSumInteger 4 17 15 i k = s_7_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_5_checked : ∀ i k : Fin 9, fourSumInteger 5 17 15 i k = s_7_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_6_checked : ∀ i k : Fin 9, fourSumInteger 6 17 15 i k = s_7_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_7_7_checked : ∀ i k : Fin 9, fourSumInteger 7 17 15 i k = s_7_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_0_checked : ∀ i k : Fin 9, fourSumInteger 0 17 17 i k = s_8_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_1_checked : ∀ i k : Fin 9, fourSumInteger 1 17 17 i k = s_8_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_2_checked : ∀ i k : Fin 9, fourSumInteger 2 17 17 i k = s_8_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_3_checked : ∀ i k : Fin 9, fourSumInteger 3 17 17 i k = s_8_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_4_checked : ∀ i k : Fin 9, fourSumInteger 4 17 17 i k = s_8_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_5_checked : ∀ i k : Fin 9, fourSumInteger 5 17 17 i k = s_8_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_6_checked : ∀ i k : Fin 9, fourSumInteger 6 17 17 i k = s_8_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_8_7_checked : ∀ i k : Fin 9, fourSumInteger 7 17 17 i k = s_8_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma sums_checked : ∀ u : Fin 9, ∀ a i k, fourSumInteger a 17 (2*u.val+1) i k = sums u a i k := by
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
end SumTable17
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate17. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate17

lemma rows_table_checked_0 : ∀ v : Fin 9, integerTableEval 17 SumTable17.sums (0 : Fin 9) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 9, integerTableEval 17 SumTable17.sums (1 : Fin 9) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 9, integerTableEval 17 SumTable17.sums (2 : Fin 9) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_3 : ∀ v : Fin 9, integerTableEval 17 SumTable17.sums (3 : Fin 9) v = Y 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_4 : ∀ v : Fin 9, integerTableEval 17 SumTable17.sums (4 : Fin 9) v = Y 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_5 : ∀ v : Fin 9, integerTableEval 17 SumTable17.sums (5 : Fin 9) v = Y 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_6 : ∀ v : Fin 9, integerTableEval 17 SumTable17.sums (6 : Fin 9) v = Y 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_7 : ∀ v : Fin 9, integerTableEval 17 SumTable17.sums (7 : Fin 9) v = Y 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_8 : ∀ v : Fin 9, integerTableEval 17 SumTable17.sums (8 : Fin 9) v = Y 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 9, ∀ v : Fin 9, integerTableEval 17 SumTable17.sums u v = Y u v := by
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
lemma rows_checked_oai (u v : Fin 9) : exactFourEval 17 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 17 SumTable17.sums SumTable17.sums_checked]
  exact rows_table_checked u v
end Certificate17
end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.Certificate17.rows_checked_oai := @OAI.LaughlinGap.RealOccupation.Certificate17.rows_checked_oai
