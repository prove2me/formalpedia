-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.bound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:55.601826+00:00
-- url     : https://prove2.me/submissions/d8dbc48b-f7e6-44da-8e81-8e2178be2eaf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {m : E → ℂ} {C s t : ℝ}
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) : 0 ≤ C := by
  have h := hC 0
  have hp : 0 < (1 + ‖(0 : E)‖ ^ 2) ^ ((s - t) / 2) := by positivity
  by_contra hneg
  push Not at hneg
  have : C * (1 + ‖(0 : E)‖ ^ 2) ^ ((s - t) / 2) < 0 := mul_neg_of_neg_of_pos hneg hp
  linarith [norm_nonneg (m 0)]
end GroundTheory.Automorphic.Sobolev
