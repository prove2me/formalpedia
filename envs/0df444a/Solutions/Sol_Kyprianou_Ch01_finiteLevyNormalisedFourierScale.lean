-- Prove2me | solution 1 for Kyprianou.Ch01.finiteLevyNormalisedFourierScale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:24:40.448977+00:00
-- url     : https://prove2.me/submissions/d93c49ad-a904-48d4-9931-48eb9840d6a5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex
open scoped ENNReal NNReal
set_option autoImplicit false
/-! A finite intensity equals its mass times its normalized probability law in Fourier integration. -/
theorem solution
    (Λ : Measure ℝ) (hfinite : Λ Set.univ < ⊤) (xi : ℝ) :
    let FM : FiniteMeasure ℝ := ⟨Λ, ⟨hfinite⟩⟩
    let ν' : Measure ℝ := (FiniteMeasure.normalize FM : Measure ℝ)
    (∫ x : ℝ,
      (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂Λ) =
      ((FM.mass : ℂ) * (charFun ν' xi - 1)) := by
  dsimp
  let FM : FiniteMeasure ℝ := ⟨Λ, ⟨hfinite⟩⟩
  let ν' : Measure ℝ := (FiniteMeasure.normalize FM : Measure ℝ)
  letI : IsProbabilityMeasure ν' := (FiniteMeasure.normalize FM).property
  have hEq : Λ = ((FM.mass : ℝ≥0∞) • ν') := by
    have hh := congrArg (fun m : FiniteMeasure ℝ => (m : Measure ℝ))
      (FiniteMeasure.self_eq_mass_smul_normalize FM)
    simpa [FM, ν'] using hh
  have hExp : Integrable (fun x : ℝ =>
      Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I)) ν' := by
    have hme : Measurable (fun x : ℝ =>
        Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I)) := by fun_prop
    apply Integrable.of_bound hme.aestronglyMeasurable 1
    filter_upwards [] with x
    simp [Complex.norm_exp, Complex.mul_re]
  have hF : (∫ x : ℝ,
      (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂ν') =
      charFun ν' xi - 1 := by
    rw [integral_sub hExp (integrable_const 1)]
    rw [charFun_apply_real]
    simp
  calc
    (∫ x : ℝ, (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂Λ) =
      (∫ x : ℝ, (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1)
        ∂((FM.mass : ℝ≥0∞) • ν')) := by rw [hEq]
    _ = (FM.mass : ℂ) * (charFun ν' xi - 1) := by
      rw [integral_smul_measure, hF]
      have hcoerce : ((FM.mass : ℝ≥0∞).toReal : ℝ) = (FM.mass : ℝ) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.toReal_ofReal (NNReal.coe_nonneg _)
      rw [hcoerce]
      simp only [Complex.real_smul]
