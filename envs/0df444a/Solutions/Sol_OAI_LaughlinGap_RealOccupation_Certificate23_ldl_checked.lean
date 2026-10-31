-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.Certificate23.ldl_checked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:27:39.499952+00:00
-- url     : https://prove2.me/submissions/dc7a2973-8c2b-4de8-af21-badb1502304e

import Mathlib
import Definitions.Def_OAIQ030L000
import Definitions.Def_OAIQ030L011
import Definitions.Def_OAIQ030L013

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

lemma ldl_checked_0 : ∀ v : Fin 12, (∑ k : Fin 12, L (0 : Fin 12) k * diag k * L v k) = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_1 : ∀ v : Fin 12, (∑ k : Fin 12, L (1 : Fin 12) k * diag k * L v k) = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_2 : ∀ v : Fin 12, (∑ k : Fin 12, L (2 : Fin 12) k * diag k * L v k) = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_3 : ∀ v : Fin 12, (∑ k : Fin 12, L (3 : Fin 12) k * diag k * L v k) = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_4 : ∀ v : Fin 12, (∑ k : Fin 12, L (4 : Fin 12) k * diag k * L v k) = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_5 : ∀ v : Fin 12, (∑ k : Fin 12, L (5 : Fin 12) k * diag k * L v k) = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_6 : ∀ v : Fin 12, (∑ k : Fin 12, L (6 : Fin 12) k * diag k * L v k) = M 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_7 : ∀ v : Fin 12, (∑ k : Fin 12, L (7 : Fin 12) k * diag k * L v k) = M 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_8 : ∀ v : Fin 12, (∑ k : Fin 12, L (8 : Fin 12) k * diag k * L v k) = M 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_9 : ∀ v : Fin 12, (∑ k : Fin 12, L (9 : Fin 12) k * diag k * L v k) = M 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_10 : ∀ v : Fin 12, (∑ k : Fin 12, L (10 : Fin 12) k * diag k * L v k) = M 10 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_11 : ∀ v : Fin 12, (∑ k : Fin 12, L (11 : Fin 12) k * diag k * L v k) = M 11 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_oai : ∀ u : Fin 12, ∀ v : Fin 12, (∑ k : Fin 12, L u k * diag k * L v k) = M u v := by
  intro u
  fin_cases u
  · exact ldl_checked_0
  · exact ldl_checked_1
  · exact ldl_checked_2
  · exact ldl_checked_3
  · exact ldl_checked_4
  · exact ldl_checked_5
  · exact ldl_checked_6
  · exact ldl_checked_7
  · exact ldl_checked_8
  · exact ldl_checked_9
  · exact ldl_checked_10
  · exact ldl_checked_11
end Certificate23
end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.Certificate23.ldl_checked_oai := @OAI.LaughlinGap.RealOccupation.Certificate23.ldl_checked_oai
