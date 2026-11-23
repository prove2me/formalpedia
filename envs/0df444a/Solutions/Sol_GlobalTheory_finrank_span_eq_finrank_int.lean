-- Prove2me | solution 1 for GlobalTheory.finrank_span_eq_finrank_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:30.772725+00:00
-- url     : https://prove2.me/submissions/cd28ffd5-7131-4db0-8d00-1b203194a314

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
theorem _root_.solution [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] : finrank ℝ (span ℝ (L : Set E)) = finrank ℤ L := by
  have h : DiscreteTopology (span ℤ (L : Set E)) := by rw [span_eq]; infer_instance
  have := Real.finrank_eq_int_finrank_of_discrete h
  rwa [Set.finrank, Set.finrank, span_eq] at this
end GlobalTheory
