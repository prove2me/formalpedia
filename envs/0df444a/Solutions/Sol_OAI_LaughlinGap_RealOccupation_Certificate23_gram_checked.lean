-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.Certificate23.gram_checked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:27:38.460383+00:00
-- url     : https://prove2.me/submissions/34a0a056-acbd-4d63-99dd-844be380e5e7

import Mathlib
import Definitions.Def_OAIQ030L000
import Definitions.Def_OAIQ030L012
import Definitions.Def_OAIQ030L013
import Definitions.Def_OAIQ030L014
import Definitions.Def_OAIQ030L017

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

lemma gram_checked_0 : ∀ v : Fin 12, (∑ a : Fin 84, columns (0 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 12, (∑ a : Fin 84, columns (1 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 12, (∑ a : Fin 84, columns (2 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_3 : ∀ v : Fin 12, (∑ a : Fin 84, columns (3 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_4 : ∀ v : Fin 12, (∑ a : Fin 84, columns (4 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_5 : ∀ v : Fin 12, (∑ a : Fin 84, columns (5 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_6 : ∀ v : Fin 12, (∑ a : Fin 84, columns (6 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_7 : ∀ v : Fin 12, (∑ a : Fin 84, columns (7 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_8 : ∀ v : Fin 12, (∑ a : Fin 84, columns (8 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_9 : ∀ v : Fin 12, (∑ a : Fin 84, columns (9 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_10 : ∀ v : Fin 12, (∑ a : Fin 84, columns (10 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 10 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_11 : ∀ v : Fin 12, (∑ a : Fin 84, columns (11 : Fin 12) a * columns v a / setFactorial (keys a)) = Z 11 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_oai : ∀ u : Fin 12, ∀ v : Fin 12, (∑ a : Fin 84, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
  · exact gram_checked_3
  · exact gram_checked_4
  · exact gram_checked_5
  · exact gram_checked_6
  · exact gram_checked_7
  · exact gram_checked_8
  · exact gram_checked_9
  · exact gram_checked_10
  · exact gram_checked_11
end Certificate23
end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.Certificate23.gram_checked_oai := @OAI.LaughlinGap.RealOccupation.Certificate23.gram_checked_oai
