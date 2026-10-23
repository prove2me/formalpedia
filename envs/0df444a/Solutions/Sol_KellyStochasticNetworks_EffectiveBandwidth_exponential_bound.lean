-- Prove2me | solution 1 for KellyStochasticNetworks.EffectiveBandwidth.exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:16:40.237408+00:00
-- url     : https://prove2.me/submissions/97392476-e6d1-47f0-b1f2-893e1775dbeb

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (s : ℝ) (hs : 0 ≤ s) :
    P {ω | 0 < Y ω} =
      (∫⁻ ω, Set.indicator {ω | 0 < Y ω} (fun _ => (1 : ℝ≥0∞)) ω ∂P) ∧
    P {ω | 0 < Y ω} ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (s * Y ω)) ∂P := by
  have hm : MeasurableSet {ω | 0 < Y ω} := measurableSet_lt measurable_const hY
  have h1 : P {ω | 0 < Y ω} =
      (∫⁻ ω, Set.indicator {ω | 0 < Y ω} (fun _ => (1 : ℝ≥0∞)) ω ∂P) := by
    rw [lintegral_indicator hm, setLIntegral_const, one_mul]
  refine ⟨h1, ?_⟩
  rw [h1]
  refine lintegral_mono fun ω => ?_
  by_cases h : 0 < Y ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | 0 < Y ω} from h)]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hs h.le))
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | 0 < Y ω} from h)]
    exact bot_le
