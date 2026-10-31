-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.Certificate23.columns_checked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T04:13:35.236909+00:00
-- url     : https://prove2.me/submissions/4241c300-862d-45a3-b319-d039e6a68648

import Mathlib
import Definitions.Def_OAIQ030L033
import Definitions.Def_OAIQ030L035

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

lemma checkVector_sound {n : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → α) (h : checkVector A B = true) : ∀ i, A i = B i := by
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

end LaughlinGap.Arithmetic

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate23

lemma columns_checked_0 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(0 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(1 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(2 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_3 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(3 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_4 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(4 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_5 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(5 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_6 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(6 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_7 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(7 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_8 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(8 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_9 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(9 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_10 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(10 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 10 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_11 : ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*(11 : Fin 12).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns 11 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_oai : ∀ u : Fin 12, ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
  · exact columns_checked_3
  · exact columns_checked_4
  · exact columns_checked_5
  · exact columns_checked_6
  · exact columns_checked_7
  · exact columns_checked_8
  · exact columns_checked_9
  · exact columns_checked_10
  · exact columns_checked_11
end Certificate23
end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.Certificate23.columns_checked_oai := @OAI.LaughlinGap.RealOccupation.Certificate23.columns_checked_oai
