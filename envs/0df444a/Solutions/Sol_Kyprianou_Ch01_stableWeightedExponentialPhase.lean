-- Prove2me | solution 1 for Kyprianou.Ch01.stableWeightedExponentialPhase
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:47:32.104185+00:00
-- url     : https://prove2.me/submissions/f2572bf7-3d3b-47c8-993a-c74a50045176

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableTwoSidedTrigSkewFactor
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem solution
    (cpos cneg theta : ℝ)
    (hsum : cpos + cneg ≠ 0)
    (hcos : Real.cos theta ≠ 0) :
    (cpos : ℂ) * Complex.exp (-(Complex.I * (theta : ℂ))) +
    (cneg : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) =
      (((cpos + cneg) * Real.cos theta : ℝ) : ℂ) *
        (1 - Complex.I *
          (((cpos - cneg) / (cpos + cneg) *
              Real.tan theta : ℝ) : ℂ)) := by
  have hm :
      Complex.exp (-(Complex.I * (theta : ℂ))) =
        (Real.cos theta : ℂ) - Complex.I * (Real.sin theta : ℂ) := by
    have he := Complex.exp_ofReal_mul_I (-theta)
    have harg : -(Complex.I * (theta : ℂ)) =
        ((-theta : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, he]
    simp only [Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hp :
      Complex.exp (Complex.I * (theta : ℂ)) =
        (Real.cos theta : ℂ) + Complex.I * (Real.sin theta : ℂ) := by
    rw [mul_comm, Complex.exp_ofReal_mul_I]
    ring
  rw [hm, hp]
  exact Kyprianou.Ch01.stableTwoSidedTrigSkewFactor
    cpos cneg theta hsum hcos
