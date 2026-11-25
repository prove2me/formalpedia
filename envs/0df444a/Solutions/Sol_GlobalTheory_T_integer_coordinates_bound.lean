-- Prove2me | solution 1 for GlobalTheory.T.integer_coordinates_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:34.845797+00:00
-- url     : https://prove2.me/submissions/e4fc8b4e-dec2-4da0-85cf-0fa033c81d14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegerCoordinatesBound
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegerCoordinatesBoundStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_NumberFieldCoord_abs_repr_le_of_forall_norm_embedding_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)), Function.Surjective (fun i => InfinitePlace.mk (τ i)) → ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) → ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by
  first | exact @GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le | exact GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le | (intros; apply GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le <;> assumption)
end _root_.GlobalTheory.T
