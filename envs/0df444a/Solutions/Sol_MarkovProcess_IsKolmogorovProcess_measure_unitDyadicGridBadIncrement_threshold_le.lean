-- Prove2me | solution 1 for MarkovProcess.IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_threshold_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:34:30.532385+00:00
-- url     : https://prove2.me/submissions/0d8c65f1-0f86-4e38-8f5e-b4727d3fc2b1

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_FiniteGridFoundations
import Definitions.Def_MarkovProcess_DyadicIncrementScalars
import Theorems.Thm_MarkovProcess_dyadic_bound_normalization
import Theorems.Thm_MarkovProcess_IsKolmogorovProcess_measure_unitDyadicGridBadIncrement_le
import Theorems.Thm_MarkovProcess_dyadicIncrementThreshold_ne_zero
import Theorems.Thm_MarkovProcess_dyadicIncrementThreshold_ne_top
open MarkovProcess MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem solution
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ) (n : ℕ) :
    P (finiteGridBadIncrement X (unitDyadicGrid n) p (dyadicIncrementThreshold γ n)) ≤
      ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) := by
  rw [← dyadic_bound_normalization p q γ M n]
  exact MarkovProcess.IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_le hX n _ (dyadicIncrementThreshold_ne_zero hγ n)
    (dyadicIncrementThreshold_ne_top hγ n)
