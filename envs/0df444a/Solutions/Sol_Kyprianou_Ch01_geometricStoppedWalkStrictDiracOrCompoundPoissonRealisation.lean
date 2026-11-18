-- Prove2me | solution 1 for Kyprianou.Ch01.geometricStoppedWalkStrictDiracOrCompoundPoissonRealisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:24:46.053986+00:00
-- url     : https://prove2.me/submissions/f4d03d85-09b4-4633-9b54-7f90161af4e7

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_Kyprianou_Ch01_geometricStoppedWalkStrictDiracOrCompoundPoissonCharFun
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-! Uniqueness of characteristic functions produces the exact law identity in either case. -/
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
    (P.map (fun ω =>
      ∑ i ∈ Finset.range (N ω), increment i ω) =
      Measure.dirac (0 : ℝ)) ∨
    ∃ (r : ℝ≥0) (ν' : Measure ℝ) (Ω' : Type)
      (_ : MeasurableSpace Ω') (μ : Measure Ω')
      (τ Y : ℕ → Ω' → ℝ),
      IsProbabilityMeasure ν' ∧
      IsProbabilityMeasure μ ∧
      0 < r ∧ ν' {0} = 0 ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ ∧
      P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω) =
        μ.map (LevyFoundations.compoundPoisson 0 τ Y (1 : ℝ)) := by
  rcases Kyprianou.Ch01.geometricStoppedWalkStrictDiracOrCompoundPoissonCharFun
      P p hp0 hp1 increment N hNmeas hIncMeas hIID
      jumpLaw hCommon hGeometric hIndependent with hzero | hcp
  · left
    apply Measure.ext_of_charFun
    funext xi
    exact hzero xi
  · right
    obtain ⟨r, ν', Ω', m, μ, τ, Y, hν, hμ, hr, hνzero, hd, hξ⟩ := hcp
    letI : MeasurableSpace Ω' := m
    letI : IsProbabilityMeasure ν' := hν
    letI : IsProbabilityMeasure μ := hμ
    refine ⟨r, ν', Ω', m, μ, τ, Y, hν, hμ, hr, hνzero, hd, ?_⟩
    apply Measure.ext_of_charFun
    funext xi
    exact hξ xi
