-- Prove2me | solution 1 for GlobalTheory.exists_add_orthogonal_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:42.695423+00:00
-- url     : https://prove2.me/submissions/1d29fb47-d29b-46ef-9992-6a7ad732bc1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution (W : Submodule ℝ E) (u : E) :
    ∃ p ∈ W, ∃ q ∈ Wᗮ, u = p + q ∧ ‖q‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  obtain ⟨p, hp, q, hq, h⟩ := W.exists_add_mem_mem_orthogonal u
  refine ⟨p, hp, q, hq, h, ?_⟩
  rw [h, norm_add_sq_real, Submodule.inner_right_of_mem_orthogonal hp hq]
  nlinarith [sq_nonneg ‖p‖]
end GlobalTheory
