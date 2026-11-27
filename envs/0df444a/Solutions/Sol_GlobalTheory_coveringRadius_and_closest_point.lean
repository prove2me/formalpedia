-- Prove2me | solution 1 for GlobalTheory.coveringRadius_and_closest_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:10.99588+00:00
-- url     : https://prove2.me/submissions/f4727ad0-ab3f-4526-9b8c-976c56f4c868

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_mem_norm_sub_le_of_linearIndependent
import Theorems.Thm_GlobalTheory_coveringRadius_le_lastMin
import Theorems.Thm_GlobalTheory_exists_closest_point
import Theorems.Thm_GlobalTheory_abs_two_mul_inner_le_of_closest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : Submodule ℤ E}
namespace GlobalTheory
theorem _root_.solution [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    (∀ (v : Fin (finrank ℝ E) → E) (r : ℝ), LinearIndependent ℝ v → (∀ i, v i ∈ L) →
      (∀ i, ‖v i‖ ≤ r) → ∀ x : E, ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℝ E) / 2 * r) ∧
    coveringRadius L ≤ √(finrank ℝ E) / 2 * lastMin L ∧
    (∀ x : E, ∃ w ∈ L, ∀ z ∈ L, ‖x - w‖ ≤ ‖x - z‖) ∧
    (∀ p : E, ∀ w ∈ L, (∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) →
      ∀ y ∈ L, |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2) :=
  ⟨fun _ _ hv hL hr => exists_mem_norm_sub_le_of_linearIndependent hv (Fintype.card_fin _) hL hr,
    coveringRadius_le_lastMin L, exists_closest_point L,
    fun _ _ hw h _ hy => abs_two_mul_inner_le_of_closest hw h hy⟩
end GlobalTheory
