-- Prove2me | solution 1 for GlobalTheory.exp_neg_mul_norm_add_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:40.33951+00:00
-- url     : https://prove2.me/submissions/beff412b-71e7-47c7-a15b-9c4007708080

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real FourierTransform
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution {a R : ℝ} (ha : 0 ≤ a) (x : E) {u : E} (hu : ‖u‖ ≤ R) :
    Real.exp (-a * ‖x + u‖ ^ 2) ≤ Real.exp (a * R ^ 2) * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : ‖x‖ ≤ ‖x + u‖ + R := by
    have := norm_sub_le (x + u) u
    rw [add_sub_cancel_right] at this
    linarith
  have h2 : ‖x‖ ^ 2 ≤ (‖x + u‖ + R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : ‖x‖ ^ 2 / 2 ≤ ‖x + u‖ ^ 2 + R ^ 2 := by nlinarith [sq_nonneg (‖x + u‖ - R)]
  nlinarith [mul_le_mul_of_nonneg_left h3 ha]
end GlobalTheory
