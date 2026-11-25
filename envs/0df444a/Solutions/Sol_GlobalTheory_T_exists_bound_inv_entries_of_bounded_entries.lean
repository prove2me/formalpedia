-- Prove2me | solution 1 for GlobalTheory.T.exists_bound_inv_entries_of_bounded_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:16:47.896067+00:00
-- url     : https://prove2.me/submissions/0b18897b-2311-4f0f-9c08-dc3dfd485723

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MatrixInvEntriesBounded
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MatrixInvEntriesBoundedStatement
import Theorems.Thm_GlobalTheory_matrix_inv_entries_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] (n : ℕ) (G : Matrix (Fin n) (Fin n) R → ℝ), Continuous G → (∀ c, G c ≠ 0 → IsUnit c) → ∀ B ε : ℝ, 0 < ε → ∃ C : ℝ, (∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → G c ≤ C) ∧ ∀ c : GL (Fin n) R, (∀ i j, ‖c.1 i j‖ ≤ B) → ε ≤ G c.1 → ∀ i j, ‖c⁻¹.1 i j‖ ≤ C := by
  first | exact @GlobalTheory.matrix_inv_entries_bounded | exact GlobalTheory.matrix_inv_entries_bounded | (intros; apply GlobalTheory.matrix_inv_entries_bounded <;> assumption)
end _root_.GlobalTheory.T
