-- Prove2me | solution 1 for Kyprianou.compoundPoissonDriftPathCriterionCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:32:39.49588+00:00
-- url     : https://prove2.me/submissions/23488e81-0c18-4c59-b580-35de3a3d220d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_Kyprianou_Ch02_compoundPoissonDriftMarginalNecessityV1
import Theorems.Thm_Kyprianou_Ch02_compoundPoissonZeroIntensityMarginalsV1
import Theorems.Thm_Kyprianou_Ch02_compoundPoissonPositiveIntensityMarginalsV1
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
    ((∃ (d : ℝ),
      (levyMeasure = 0 ∧
       ∀ (t : ℝ≥0), ∀ᵐ ω ∂P, X t ω = d * (t : ℝ)) ∨
      (∃ (r : ℝ≥0) (hr : 0 < r)
         (F : Measure ℝ) (hF : IsProbabilityMeasure F),
         letI : IsProbabilityMeasure F := hF
         levyMeasure = (r : ENNReal) • F ∧
         ∃ (Ω' : Type) (measΩ' : MeasurableSpace Ω'),
           letI : MeasurableSpace Ω' := measΩ'
           ∃ (P' : Measure Ω') (hP' : IsProbabilityMeasure P'),
             letI : IsProbabilityMeasure P' := hP'
             ∃ (τ Y : ℕ → Ω' → ℝ),
               LevyFoundations.IsCompoundPoissonDriver τ Y r F P' ∧
               ∀ (t : ℝ≥0),
                 P.map (X t) =
                   P'.map (fun ω =>
                     LevyFoundations.compoundPoisson d τ Y (t : ℝ) ω))) ↔
     σ = 0 ∧ levyMeasure Set.univ < ⊤) := by
  constructor
  · exact Kyprianou.Ch02.compoundPoissonDriftMarginalNecessityV1
      a σ levyMeasure hlevyMeasure P X hX hchar
  · rintro ⟨hσ, hfinite⟩
    by_cases hz : levyMeasure = 0
    · exact ⟨-a, Or.inl ⟨hz,
        Kyprianou.Ch02.compoundPoissonZeroIntensityMarginalsV1
          a σ levyMeasure hlevyMeasure P X hX hchar hσ hz⟩⟩
    · have hp : 0 < levyMeasure Set.univ :=
        pos_iff_ne_zero.mpr (fun h => hz (Measure.measure_univ_eq_zero.mp h))
      obtain ⟨d, hd⟩ := Kyprianou.Ch02.compoundPoissonPositiveIntensityMarginalsV1
        a σ levyMeasure hlevyMeasure P X hX hchar hσ hfinite hp
      exact ⟨d, Or.inr hd⟩
