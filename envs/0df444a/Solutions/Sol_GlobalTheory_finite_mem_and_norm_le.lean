-- Prove2me | solution 1 for GlobalTheory.finite_mem_and_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:40.393036+00:00
-- url     : https://prove2.me/submissions/229273ca-852e-43a6-af05-c71dc7bd461c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin

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
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}
namespace GlobalTheory
theorem _root_.solution [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (R : ℝ) : {x : E | x ∈ L ∧ ‖x‖ ≤ R}.Finite := by
  have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  have h : (Metric.closedBall (0 : E) R ∩ L.toAddSubgroup).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall inferInstance
  exact h.subset fun x hx => ⟨mem_closedBall_zero_iff.2 hx.2, hx.1⟩
end GlobalTheory
