-- Prove2me | solution 1 for Kyprianou.Ch04.stoppedAbsoluteMassFromBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:40:03.390344+00:00
-- url     : https://prove2.me/submissions/b94b9938-a047-4aa5-908b-333abdc08e4a

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A uniform bound on the stopped positive-time mark integral yields finite expected mass. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (nu : Measure ℝ) (k : ℝ → ℝ → Ω → ℝ) (tau : Ω → WithTop NNReal)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hb : ∀ᵐ w ∂P, ∀ s : ℝ, 0 < s → (s.toNNReal : WithTop NNReal) ≤ tau w →
      (∫⁻ x, ENNReal.ofReal |k s x w| ∂nu) ≤ B) (t : NNReal) :
    (∫⁻ w, ∫⁻ s in Icc (0 : ℝ) (t : ℝ), ∫⁻ x,
      ENNReal.ofReal |if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0|
      ∂nu ∂volume ∂P) < ⊤ := by
  have hbound : ∀ᵐ w ∂P, (∫⁻ s in Icc (0 : ℝ) (t : ℝ), ∫⁻ x,
      ENNReal.ofReal |if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0|
      ∂nu ∂volume) ≤ B * (volume (Icc (0 : ℝ) (t : ℝ))) := by
    filter_upwards [hb] with w hw
    calc
      _ ≤ ∫⁻ s in Icc (0 : ℝ) (t : ℝ), B ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc,
          ae_restrict_of_ae ((Set.countable_singleton (0 : ℝ)).ae_notMem volume)] with s hs hz
        by_cases h : (s.toNNReal : WithTop NNReal) ≤ tau w
        · simp only [if_pos h]
          exact hw s (lt_of_le_of_ne hs.1 (Ne.symm hz)) h
        · simp only [if_neg h,abs_zero,ENNReal.ofReal_zero,lintegral_zero]
          exact zero_le
      _ = _ := by simp [Measure.restrict_apply_univ]
  refine lt_of_le_of_lt (lintegral_mono_ae hbound) ?_
  rw [lintegral_const,measure_univ,mul_one]
  exact ENNReal.mul_lt_top hB (by simp [Real.volume_Icc])
