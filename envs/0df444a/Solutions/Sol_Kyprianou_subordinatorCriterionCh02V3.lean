-- Prove2me | solution 1 for Kyprianou.subordinatorCriterionCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:29:13.710045+00:00
-- url     : https://prove2.me/submissions/bd693493-6f1c-4d8b-9d39-963828041e2e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

import Theorems.Thm_Kyprianou_Ch02_subordinatorMarginalNecessityV1
import Theorems.Thm_Kyprianou_Ch02_subordinatorMarginalSufficiencyV1
import Theorems.Thm_Kyprianou_Ch02_levyMonotoneOfNonnegativeMarginalsV1
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou

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
    (∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω)) ↔
    levyMeasure (Set.Iio (0 : ℝ)) = 0 ∧
    σ = 0 ∧
    Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (levyMeasure.restrict (Set.Ioi (0 : ℝ))) ∧
    0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure := by
  constructor
  · intro hm
    apply Kyprianou.Ch02.subordinatorMarginalNecessityV1
      a σ levyMeasure hlevyMeasure P X hX hchar
    intro t
    filter_upwards [hm] with ω hω
    have h := hω (show (0 : ℝ≥0) ≤ t from zero_le)
    have hzero : X 0 ω = 0 := congrFun hX.start_zero ω
    simpa [hzero] using h
  · intro h
    exact Kyprianou.Ch02.levyMonotoneOfNonnegativeMarginalsV1 P X hX
      (Kyprianou.Ch02.subordinatorMarginalSufficiencyV1
        a σ levyMeasure hlevyMeasure P X hX hchar h)
