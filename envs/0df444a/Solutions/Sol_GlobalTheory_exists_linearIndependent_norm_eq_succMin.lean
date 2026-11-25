-- Prove2me | solution 1 for GlobalTheory.exists_linearIndependent_norm_eq_succMin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:50.725797+00:00
-- url     : https://prove2.me/submissions/56847088-e2a6-405f-8b1c-4d3e8d32429a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Theorems.Thm_GlobalTheory_exists_linearIndependent_eq_succMinOf
import Theorems.Thm_GlobalTheory_finite_mem_and_norm_le
import Theorems.Thm_GlobalTheory_natCast_le_rank_of_le_finrank


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
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {n : ℕ}
variable [FiniteDimensional ℝ E] [DiscreteTopology L]
namespace GlobalTheory
theorem _root_.solution (hn : n ≤ finrank ℝ (span ℝ (L : Set E))) :
    ∃ v : Fin n → E, LinearIndependent ℝ v ∧ (∀ j, v j ∈ L) ∧
      ∀ j : Fin n, ‖v j‖ = succMin L (j + 1) :=
  exists_linearIndependent_eq_succMinOf (N := fun x : E => ‖x‖) (S := (L : Set E))
    (finite_mem_and_norm_le L) (fun x _ => norm_nonneg x) (natCast_le_rank_of_le_finrank hn)
end GlobalTheory
