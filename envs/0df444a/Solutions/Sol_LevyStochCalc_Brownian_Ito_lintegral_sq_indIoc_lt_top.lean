-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_sq_indIoc_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:02:58.129937+00:00
-- url     : https://prove2.me/submissions/0498fe82-dc7a-4175-aef4-1b451fb2269f

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000
open MeasureTheory LevyStochCalc.Brownian.Ito
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (a b : ℝ)
    (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  calc
    _ ≤ ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (1 : ℝ≥0∞) ∂volume ∂P := by
      apply lintegral_mono
      intro ω
      apply lintegral_mono
      intro s
      by_cases h : s ∈ Set.Ioc a b <;> simp [indIoc, h]
    _ < ⊤ := by simp [Real.volume_Icc]
