-- Prove2me | solution 2 for Kyprianou.Ch01.stableAlphaAboveOneKernelValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:38:54.504465+00:00
-- url     : https://prove2.me/submissions/7d3fe834-1115-45ab-91df-546addff33d7

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedIntegrationByParts
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueImaginary
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneGammaPhaseAlgebra
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
      ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ))) := by
  have hbeta0 : 0 < alpha - 1 := by linarith
  have hbeta1 : alpha - 1 < 1 := by linarith
  have hneg : -(alpha - 1) = 1 - alpha := by ring
  have hdef :=
    Kyprianou.Ch01.stableGammaComplexDeficitValueImaginary
      (alpha - 1) hbeta0 hbeta1 Complex.I
      (by simp) (by simp) (by simp)
  have hdef' :
      (∫ r in Set.Ioi (0 : ℝ),
        (Complex.exp (Complex.I * (r : ℂ)) - 1) *
          (((r ^ (-(alpha - 1) - 1) : ℝ)) : ℂ)
        ∂volume) =
      ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
        Complex.exp (((alpha - 1 : ℝ) : ℂ) *
          Complex.log (-Complex.I)) := by
    simpa only [hneg] using hdef
  calc
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
      ∂volume) =
      (Complex.I / (alpha : ℂ)) *
        (∫ r in Set.Ioi (0 : ℝ),
          (Complex.exp (Complex.I * (r : ℂ)) - 1) *
            (((r ^ (-(alpha - 1) - 1) : ℝ)) : ℂ)
          ∂volume) :=
        Kyprianou.Ch01.stableAlphaAboveOneCompensatedIntegrationByParts
          alpha ha1 ha2
    _ = (Complex.I / (alpha : ℂ)) *
          (((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
            Complex.exp (((alpha - 1 : ℝ) : ℂ) *
              Complex.log (-Complex.I))) := by rw [hdef']
    _ = ((Real.Gamma (-alpha) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I *
            ((Real.pi * alpha / 2 : ℝ) : ℂ))) :=
        Kyprianou.Ch01.stableAlphaAboveOneGammaPhaseAlgebra
          alpha ha1 ha2
    _ = ((Real.Gamma (-alpha) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I *
            ((Real.pi * alpha / 2) : ℂ))) := by
        push_cast
        all_goals ring
