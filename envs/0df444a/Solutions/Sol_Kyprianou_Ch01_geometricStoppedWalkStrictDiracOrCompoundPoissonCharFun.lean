-- Prove2me | solution 1 for Kyprianou.Ch01.geometricStoppedWalkStrictDiracOrCompoundPoissonCharFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:26:54.607702+00:00
-- url     : https://prove2.me/submissions/78a875db-436f-4eee-8e9f-bc6e730ce1f7

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_Kyprianou_Ch01_geometricStoppedIIDFiniteLevyIntensity
import Theorems.Thm_Kyprianou_Ch01_geometricStoppedIIDCharFun
import Theorems.Thm_Kyprianou_Ch01_positiveFiniteLevyIntensityCompoundPoissonCharFun
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ,
      HasLaw (increment n) jumpLaw P)
    (hGeometric : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal (p * (1 - p) ^ k))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P) :
    (∀ xi : ℝ,
      charFun (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
      charFun (Measure.dirac (0 : ℝ)) xi) ∨
    ∃ (r : ℝ≥0) (ν' : Measure ℝ) (Ω' : Type)
      (_ : MeasurableSpace Ω') (μ : Measure Ω')
      (τ Y : ℕ → Ω' → ℝ),
      IsProbabilityMeasure ν' ∧
      IsProbabilityMeasure μ ∧
      0 < r ∧ ν' {0} = 0 ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ ∧
      (∀ xi : ℝ,
        charFun (P.map (fun ω =>
          ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
        charFun (μ.map (LevyFoundations.compoundPoisson 0 τ Y (1 : ℝ))) xi) := by
  obtain ⟨Λ, hzero, hfinite, hFourier⟩ :=
    Kyprianou.Ch01.geometricStoppedIIDFiniteLevyIntensity
      P p hp0 hp1 increment N hNmeas hIncMeas hIID jumpLaw
      hCommon hGeometric hIndependent
  have hChar := Kyprianou.Ch01.geometricStoppedIIDCharFun
    P p hp0 hp1 increment N hNmeas hIncMeas hIID jumpLaw
    hCommon hGeometric hIndependent
  by_cases hz : Λ Set.univ = 0
  · have hΛ : Λ = 0 := Measure.measure_univ_eq_zero.mp hz
    left
    intro xi
    have hratio :
        (p : ℂ) / (1 - (((1 - p : ℝ) : ℂ) * charFun jumpLaw xi)) =
        1 := by
      have hh := (hFourier xi).2
      simpa [hΛ] using hh.symm
    rw [hChar xi]
    simpa [charFun_dirac] using hratio
  · have hpΛ : 0 < Λ Set.univ :=
      lt_of_le_of_ne (zero_le : (0 : ℝ≥0∞) ≤ Λ Set.univ) (Ne.symm hz)
    obtain ⟨r, ν', Ω', m, μ, τ, Y, hν, hμ, hr, hνzero, hd, hCP⟩ :=
      Kyprianou.Ch01.positiveFiniteLevyIntensityCompoundPoissonCharFun
        Λ hfinite hpΛ hzero
    right
    refine ⟨r, ν', Ω', m, μ, τ, Y, hν, hμ, hr, hνzero, hd, ?_⟩
    intro xi
    calc
      charFun (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
        (p : ℂ) / (1 - (((1 - p : ℝ) : ℂ) * charFun jumpLaw xi)) :=
          hChar xi
      _ = Complex.exp
        (∫ x : ℝ,
          (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂Λ) :=
            (hFourier xi).2.symm
      _ = charFun (μ.map
        (LevyFoundations.compoundPoisson 0 τ Y (1 : ℝ))) xi :=
          (hCP xi).symm
