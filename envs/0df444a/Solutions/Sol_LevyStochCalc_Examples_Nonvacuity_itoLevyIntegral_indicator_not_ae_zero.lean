-- Prove2me | solution 1 for LevyStochCalc.Examples.Nonvacuity.itoLevyIntegral_indicator_not_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T06:26:06.640675+00:00
-- url     : https://prove2.me/submissions/fa351978-5d81-43bf-aa8d-d562969903ac

import Theorems.Thm_LevyStochCalc_Examples_Nonvacuity_markedProgressivelyMeasurable_indicator_mark
import Definitions.Def_NonvacuityDrivers_F001

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open LevyStochCalc.Examples.Nonvacuity

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hApos : 0 < ν A) {T : ℝ} (hT : 0 < T) :
    ¬ LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ
        (fun _ _ e => A.indicator (fun _ => (1 : ℝ)) e)
        (measurable_indicator_mark hA)
        (markedProgressivelyMeasurable_indicator_mark ℱ hA)
        (lintegral_sq_indicator_mark_lt_top hA hAν) T
      =ᵐ[P] fun _ => (0 : ℝ) := by
  intro h0
  have hsq := lintegral_sq_itoLevyIntegral_indicator (N := N) (ℱ := ℱ) hℱ hA hAν hT
  have hzero :
      ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ
        (fun _ _ e => A.indicator (fun _ => (1 : ℝ)) e)
        (measurable_indicator_mark hA)
        (markedProgressivelyMeasurable_indicator_mark ℱ hA)
        (lintegral_sq_indicator_mark_lt_top hA hAν) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
    rw [lintegral_congr_ae (by
      filter_upwards [h0] with ω h
      rw [h])]
    simp
  rw [hzero] at hsq
  exact (mul_ne_zero hApos.ne' (ENNReal.ofReal_ne_zero_iff.mpr hT)) hsq.symm
