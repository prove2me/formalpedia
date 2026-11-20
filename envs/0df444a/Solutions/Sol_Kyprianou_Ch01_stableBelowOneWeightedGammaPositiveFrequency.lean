-- Prove2me | solution 1 for Kyprianou.Ch01.stableBelowOneWeightedGammaPositiveFrequency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:52:06.484264+00:00
-- url     : https://prove2.me/submissions/2d506463-56b6-4c58-9e60-2929a3699508

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableGammaPositiveFrequencyPhase
import Theorems.Thm_Kyprianou_Ch01_stableGammaNegativeFrequencyPhase
import Theorems.Thm_Kyprianou_Ch01_stableWeightedExponentialPhase
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem solution
    (alpha cpos cneg xi : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hxi : 0 < xi) (hnonzero : 0 < cpos + cneg) :
    let E : ℝ → ℂ := (fun z : ℝ => if z = 0 then (0 : ℂ) else
      Complex.exp ((alpha : ℂ) *
        Complex.log (-(Complex.I * (z : ℂ)))));
    -((Real.Gamma (-alpha) : ℝ) : ℂ) *
      ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) =
      (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) *
          (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) *
        (1 - Complex.I *
          (((((cpos - cneg) / (cpos + cneg)) *
            Real.tan (Real.pi * alpha / 2) : ℝ) : ℂ))) := by
  intro E
  let theta : ℝ := Real.pi * alpha / 2
  have hxp : xi ≠ 0 := ne_of_gt hxi
  have hxn : -xi ≠ 0 := neg_ne_zero.mpr hxp
  have hs : cpos + cneg ≠ 0 := ne_of_gt hnonzero
  have htheta1 : theta < Real.pi / 2 := by
    dsimp [theta]
    nlinarith [mul_lt_mul_of_pos_left ha1 Real.pi_pos]
  have hthetapos : 0 < theta := by
    dsimp [theta]
    positivity
  have hc : Real.cos theta ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], htheta1⟩)
  have hepos : E xi =
      (((xi ^ alpha : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * (theta : ℂ))) := by
    dsimp [E, theta]
    rw [if_neg hxp]
    exact Kyprianou.Ch01.stableGammaPositiveFrequencyPhase
      alpha xi hxi
  have heneg : E (-xi) =
      (((xi ^ alpha : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (theta : ℂ)) := by
    dsimp [E, theta]
    rw [if_neg hxn]
    simpa only [abs_neg, abs_of_pos hxi] using
      (Kyprianou.Ch01.stableGammaNegativeFrequencyPhase
        alpha (-xi) (by linarith))
  have hh :=
    Kyprianou.Ch01.stableWeightedExponentialPhase
      cpos cneg theta hs hc
  rw [hepos, heneg, abs_of_pos hxi]
  calc
    _ = -((Real.Gamma (-alpha) : ℝ) : ℂ) *
        (((xi ^ alpha : ℝ) : ℂ) *
          ((cpos : ℂ) *
            Complex.exp (-(Complex.I * (theta : ℂ))) +
           (cneg : ℂ) *
            Complex.exp (Complex.I * (theta : ℂ)))) := by ring
    _ = -((Real.Gamma (-alpha) : ℝ) : ℂ) *
        (((xi ^ alpha : ℝ) : ℂ) *
          (((cpos + cneg) * Real.cos theta : ℝ) : ℂ) *
          (1 - Complex.I *
            (((cpos - cneg) / (cpos + cneg) *
              Real.tan theta : ℝ) : ℂ))) := by rw [hh]; ring
    _ = _ := by dsimp [theta]; push_cast; ring
