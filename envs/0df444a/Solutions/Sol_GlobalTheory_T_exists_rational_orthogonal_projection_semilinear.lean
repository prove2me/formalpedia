-- Prove2me | solution 1 for GlobalTheory.T.exists_rational_orthogonal_projection_semilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:39:44.065604+00:00
-- url     : https://prove2.me/submissions/cf8be6d1-b790-43d6-a2ab-d0ff63b4b458

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalOrthogonalProjectionSemilinear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalOrthogonalProjectionSemilinearStatement
import Theorems.Thm_GlobalTheory_exists_mem_sub_mem_orthogonal_span_of_inner_mem_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W), (∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) → ∀ (N : Submodule K (Fin n → K)) (x : Fin n → K), ∃ y ∈ N, j x - j y ∈ (Submodule.span ℂ (j '' (N : Set (Fin n → K))))ᗮ := by
  first | exact @GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range | exact GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range | (intros; apply GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range <;> assumption)
end _root_.GlobalTheory.T
