-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicConvIntensityOffZeroFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:14:05.603699+00:00
-- url     : https://prove2.me/submissions/d9543e17-df35-4735-ad83-4d69cddcfcf2

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Theorems.Thm_Kyprianou_Ch01_logarithmicWeightedProbabilityMeasureSumFinite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory QueueingFundamentals.MG1
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
/-! Finite logarithmically weighted convolution measure with zero-valued clusters removed. -/
theorem solution
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw] :
    let Λ : Measure ℝ :=
      (Measure.sum fun n : ℕ =>
        (ENNReal.ofReal (q ^ (n + 1) / (n + 1 : ℝ))) •
          QueueingFundamentals.MG1.convPow jumpLaw (n + 1)).restrict ({0}ᶜ)
    Λ {0} = 0 ∧ Λ Set.univ < ⊤ := by
  dsimp
  have hprob : ∀ n : ℕ, IsProbabilityMeasure
      (QueueingFundamentals.MG1.convPow jumpLaw n) := by
    intro n
    induction n with
    | zero =>
        dsimp [QueueingFundamentals.MG1.convPow]
        exact Measure.dirac.isProbabilityMeasure
    | succ n ih =>
        letI := ih
        dsimp [QueueingFundamentals.MG1.convPow]
        exact Measure.probabilitymeasure_of_probabilitymeasures_conv _ _
  have hmass :
      (Measure.sum fun n : ℕ =>
        (ENNReal.ofReal (q ^ (n + 1) / (n + 1 : ℝ))) •
          QueueingFundamentals.MG1.convPow jumpLaw (n + 1)) Set.univ < ⊤ :=
    Kyprianou.Ch01.logarithmicWeightedProbabilityMeasureSumFinite q hq0 hq1
      (fun n => QueueingFundamentals.MG1.convPow jumpLaw (n + 1))
      (fun n => hprob (n + 1))
  constructor
  · rw [Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    simp
  · rw [Measure.restrict_apply MeasurableSet.univ]
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) hmass
