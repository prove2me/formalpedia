-- Prove2me | solution 1 for Kyprianou.Ch02.complexLaplaceAffineKernelDerivativeBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:21.243258+00:00
-- url     : https://prove2.me/submissions/7e16fac5-a879-416a-a34a-1d83910e9101

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceDerivativeUniformBoundV1
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    (b : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : r ≤ z.re)
    (x : ℝ) (hx : 0 ≤ x) :
    ‖b * (-(x : ℂ)) * Complex.exp (-z * (x : ℂ))‖ ≤
      (‖b‖ * max 1 (1 / r)) * min 1 |x| := by
  rw [mul_assoc, show -(x : ℂ) * Complex.exp (-z * (x : ℂ)) =
    -((x : ℂ) * Complex.exp (-z * (x : ℂ))) by ring, norm_mul, norm_neg]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (Kyprianou.Ch02.complexLaplaceDerivativeUniformBoundV1 r hr z hz x hx) (norm_nonneg b)
