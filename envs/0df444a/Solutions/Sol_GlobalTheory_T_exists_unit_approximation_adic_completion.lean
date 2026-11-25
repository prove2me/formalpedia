-- Prove2me | solution 1 for GlobalTheory.T.exists_unit_approximation_adic_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:20:05.586714+00:00
-- url     : https://prove2.me/submissions/a20fbd1e-049a-4851-b09b-213ba6eac0f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitApproximationAdicCompletion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitApproximationAdicCompletionStatement
import Theorems.Thm_GlobalTheory_finite_alg_hom_ker_coker_killed_of_onto_mod_ideal


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (M N : Type) [CommRing M] [Algebra A M] [Module.Finite A M] [CommRing N] [Algebra A N] [Module.Finite A N] (φ : M →ₐ[A] N), (∀ y : N, ∃ t : M, y - φ t ∈ J.map (algebraMap A N)) → (∀ (n : ℕ) (t : M), φ t ∈ (J ^ n).map (algebraMap A N) → t ∈ (J ^ n).map (algebraMap A M)) → ∃ f : A, f - 1 ∈ J ∧ (∀ y : N, algebraMap A N f * y ∈ Set.range φ) ∧ ∀ t : M, φ t = 0 → algebraMap A M f * t = 0 := by
  first | exact @GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal | exact GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal | (intros; apply GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal <;> assumption)
end _root_.GlobalTheory.T
