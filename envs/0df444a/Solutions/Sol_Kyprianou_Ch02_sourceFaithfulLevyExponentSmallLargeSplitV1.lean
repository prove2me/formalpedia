-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulLevyExponentSmallLargeSplitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:55:55.23761+00:00
-- url     : https://prove2.me/submissions/d794f266-aae7-42e6-9204-2ef1b2c26e8e

import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (ξ : ℝ) :
    Kyprianou.Ch01.levyTripleExponent
      ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ =
    (Complex.I * (((-a) * ξ : ℝ) : ℂ) -
      (((((σ ^ 2 : ℝ≥0) : ℝ) * ξ ^ 2 / 2 : ℝ)) : ℂ)) +
    (∫ x in Set.Ioo (-1 : ℝ) 1,
      ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) +
    (∫ x in (Set.Ioo (-1 : ℝ) 1)ᶜ,
      ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) := by
  have hint :
      Integrable
        (ProbabilityTheory.levyCompensatedIntegrand ξ) levyMeasure :=
    ProbabilityTheory.integrable_levyCompensatedIntegrand hlevyMeasure ξ
  have hsplit :=
    MeasureTheory.integral_add_compl
      (μ := levyMeasure) (f := ProbabilityTheory.levyCompensatedIntegrand ξ)
      (s := Set.Ioo (-1 : ℝ) 1) measurableSet_Ioo hint
  simp only [Kyprianou.Ch01.levyTripleExponent]
  rw [← hsplit]
  ring
