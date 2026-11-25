-- Prove2me | solution 1 for GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:17:46.722295+00:00
-- url     : https://prove2.me/submissions/083c04c0-b97d-4d6f-944c-28df94a203fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoordsNoHomogeneousRelationGenericHyperpla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoordsNoHomogeneousRelationGenericHyperplaStatement
import Theorems.Thm_GlobalTheory_exists_coordinates_no_homogeneous_relation_of_generic_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ), (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 → (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N, ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d → MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by
  first | exact @GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero | exact GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero | (intros; apply GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero <;> assumption)
end _root_.GlobalTheory.T
