-- Prove2me | solution 1 for Kyprianou.boundedVariationCriterionCh02
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:55:02.045349+00:00
-- url     : https://prove2.me/submissions/f05b750a-ce4b-4160-99a8-7c05fd248f42

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyBoundedVariationNecessityV1
import Theorems.Thm_Kyprianou_Ch02_levyBoundedVariationSufficiencyV1
open MeasureTheory ProbabilityTheory Complex Kyprianou
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
    (∀ᵐ ω ∂P, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => X t ω) Set.univ) ↔
    σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure := by
  constructor
  · exact Kyprianou.Ch02.levyBoundedVariationNecessityV1
      a σ levyMeasure hlevyMeasure P X hX hchar
  · exact Kyprianou.Ch02.levyBoundedVariationSufficiencyV1
      a σ levyMeasure hlevyMeasure P X hX hchar
