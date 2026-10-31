-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.Certificate23.product_checked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:46:42.538566+00:00
-- url     : https://prove2.me/submissions/db8556e7-1b5b-48c9-9318-052a9f77b8ac

import Mathlib
import Definitions.Def_OAIQ030L013
import Definitions.Def_OAIQ030L028

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

lemma product_checked_0 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (0 : Fin 12) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (1 : Fin 12) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (2 : Fin 12) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_3 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (3 : Fin 12) v = W 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_4 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (4 : Fin 12) v = W 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_5 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (5 : Fin 12) v = W 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_6 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (6 : Fin 12) v = W 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_7 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (7 : Fin 12) v = W 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_8 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (8 : Fin 12) v = W 8 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_9 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (9 : Fin 12) v = W 9 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_10 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (10 : Fin 12) v = W 10 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_11 : ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) (11 : Fin 12) v = W 11 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_oai : ∀ u : Fin 12, ∀ v : Fin 12, (Z * tableComparison 23 (1/200000) Y) u v = W u v := by
  intro u
  fin_cases u
  · exact product_checked_0
  · exact product_checked_1
  · exact product_checked_2
  · exact product_checked_3
  · exact product_checked_4
  · exact product_checked_5
  · exact product_checked_6
  · exact product_checked_7
  · exact product_checked_8
  · exact product_checked_9
  · exact product_checked_10
  · exact product_checked_11
end Certificate23
end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.Certificate23.product_checked_oai := @OAI.LaughlinGap.RealOccupation.Certificate23.product_checked_oai
