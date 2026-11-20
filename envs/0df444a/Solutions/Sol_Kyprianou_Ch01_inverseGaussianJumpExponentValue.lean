-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianJumpExponentValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T13:07:10.645827+00:00
-- url     : https://prove2.me/submissions/9c20c656-726c-4257-942c-0033df5b9e67

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianWeightedFourierGammaIdentity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    ∀ theta : ℝ,
      (∫ x in Set.Ioi (0 : ℝ),
        ((1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂Pi) =
        Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
          2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by
  intro Pi
  intro theta
  let f : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal
      ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2)))
  let mu : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let g : ℝ → ℂ := fun x =>
    (1 : ℂ) - Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hfin : ∀ᵐ x ∂mu.restrict (Set.Ioi (0 : ℝ)), f x < ⊤ := by
    filter_upwards [] with x
    exact ENNReal.ofReal_lt_top
  have h := setIntegral_withDensity_eq_setIntegral_toReal_smul₀'
    (μ := mu) (f := f) (Set.Ioi (0 : ℝ)) hf.aemeasurable hfin g
  have hweight :
      (∫ x in Set.Ioi (0 : ℝ), g x ∂(mu.withDensity f)) =
      (∫ x in Set.Ioi (0 : ℝ), (f x).toReal • g x ∂volume) := by
    simpa [mu, Measure.restrict_restrict, Set.inter_self] using h
  calc
    (∫ x in Set.Ioi (0 : ℝ),
      ((1 : ℂ) -
        Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂
          (volume.restrict (Set.Ioi (0 : ℝ))).withDensity f) =
      (∫ x in Set.Ioi (0 : ℝ),
        (f x).toReal •
          ((1 : ℂ) -
            Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂volume) := by
        simpa only [mu, g] using hweight
    _ = _ :=
      Kyprianou.Ch01.inverseGaussianWeightedFourierGammaIdentity b hb theta
