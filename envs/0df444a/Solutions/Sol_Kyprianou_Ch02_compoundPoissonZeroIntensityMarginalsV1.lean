-- Prove2me | solution 1 for Kyprianou.Ch02.compoundPoissonZeroIntensityMarginalsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:33:37.372829+00:00
-- url     : https://prove2.me/submissions/5ede7d59-626b-47d6-9080-84f509366cef

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    σ = 0 → levyMeasure = 0 →
    (∀ (t : ℝ≥0), ∀ᵐ ω ∂P, X t ω = (-a) * (t : ℝ)) := by
  intro hσ hz t
  have hmx : AEMeasurable (X t) P := by
    have h := (hX.stationary_increments 0 t).aemeasurable_snd
    have heq : increment X 0 t = X t := by
      funext ω
      change X t ω - X 0 ω = X t ω
      rw [congrFun hX.start_zero ω, sub_zero]
    rwa [heq] at h
  letI : IsProbabilityMeasure (P.map (X t)) := Measure.isProbabilityMeasure_map hmx
  have heq : P.map (X t) = Measure.dirac ((-a) * (t : ℝ)) := by
    apply Measure.ext_of_charFun
    funext ξ
    rw [hchar t ξ, charFun_dirac]
    congr 1
    simp [Kyprianou.Ch01.levyTripleExponent, hσ, hz, real_inner_comm,
      Real.inner_apply]
    ring
  have hlaw : HasLaw (X t) (Measure.dirac ((-a) * (t : ℝ))) P :=
    ⟨hmx, heq⟩
  exact hlaw.ae_eq_of_dirac
