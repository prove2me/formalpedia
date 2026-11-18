-- Prove2me | solution 1 for Kyprianou.Ch01.positiveFiniteLevyIntensityCompoundPoissonCharFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:26:36.415226+00:00
-- url     : https://prove2.me/submissions/c5b775ed-2e1c-46bb-add9-16677a14e5fa

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_levy_foundations_compoundPoissonDriverExists
import Theorems.Thm_Kyprianou_Ch01_finiteLevyNormalizeNoZeroAtom
import Theorems.Thm_Kyprianou_Ch01_finiteLevyNormalisedFourierScale
import Theorems.Thm_levy_foundations_compoundPoissonCharFun
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
/-! Any positive finite nonzero-jump Lévy intensity has a genuine CP Fourier realisation. -/
theorem solution
    (Λ : Measure ℝ) (hfinite : Λ Set.univ < ⊤)
    (hpos : 0 < Λ Set.univ) (hzero : Λ {0} = 0) :
    ∃ (r : ℝ≥0) (ν' : Measure ℝ) (Ω' : Type)
      (_ : MeasurableSpace Ω') (μ : Measure Ω')
      (τ Y : ℕ → Ω' → ℝ),
      IsProbabilityMeasure ν' ∧
      IsProbabilityMeasure μ ∧
      0 < r ∧ ν' {0} = 0 ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ ∧
      ∀ xi : ℝ,
        charFun (μ.map (LevyFoundations.compoundPoisson 0 τ Y (1 : ℝ))) xi =
          Complex.exp
            (∫ x : ℝ,
              (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂Λ) := by
  let FM : FiniteMeasure ℝ := ⟨Λ, ⟨hfinite⟩⟩
  let ν' : Measure ℝ := (FiniteMeasure.normalize FM : Measure ℝ)
  have hNonzero : FM ≠ 0 := by
    intro h
    have hz : Λ Set.univ = 0 := by
      have heq := congrArg (fun m : FiniteMeasure ℝ => (m : Measure ℝ)) h
      simpa [FM] using congrArg (fun m : Measure ℝ => m Set.univ) heq
    exact (ne_of_gt hpos) hz
  have hr : 0 < FM.mass :=
    lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ FM.mass)
      (Ne.symm (FM.mass_nonzero_iff.mpr hNonzero))
  have hν : IsProbabilityMeasure ν' := (FiniteMeasure.normalize FM).property
  letI : IsProbabilityMeasure ν' := hν
  have hνzero : ν' {0} = 0 :=
    Kyprianou.Ch01.finiteLevyNormalizeNoZeroAtom Λ hfinite hpos hzero
  obtain ⟨Ω', m, μ, τ, Y, hμ, hd⟩ :=
    levy_foundations_compoundPoissonDriverExists FM.mass hr ν'
  letI : MeasurableSpace Ω' := m
  letI : IsProbabilityMeasure μ := hμ
  refine ⟨FM.mass, ν', Ω', m, μ, τ, Y, hν, hμ, hr, hνzero, hd, ?_⟩
  intro xi
  have hFourier :=
    Kyprianou.Ch01.finiteLevyNormalisedFourierScale Λ hfinite xi
  change (∫ x : ℝ,
      (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂Λ) =
      (FM.mass : ℂ) * (charFun ν' xi - 1) at hFourier
  have hChar :=
    levy_foundations_compoundPoissonCharFun hd hr 0 (1 : ℝ≥0) xi
  simp only [NNReal.coe_one] at hChar
  rw [hChar]
  simp only [Complex.ofReal_one, one_mul, zero_mul,
    Complex.ofReal_zero, zero_add, mul_zero]
  exact congrArg Complex.exp hFourier.symm
