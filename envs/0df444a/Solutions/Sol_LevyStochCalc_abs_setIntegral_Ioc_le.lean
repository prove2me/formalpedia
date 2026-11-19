-- Prove2me | solution 1 for LevyStochCalc.abs_setIntegral_Ioc_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:52:51.486205+00:00
-- url     : https://prove2.me/submissions/ae640b9c-f37c-4a65-9f57-93b4583dfb09

import Definitions.Def_LevyStochCalc_Brownian_DriftIncrement_F000

open MeasureTheory

theorem solution {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (hab : a ≤ b) :
    |∫ s in Set.Ioc a b, f s ∂volume| ≤ B * (b - a) := by
  have hnorm : ∀ s ∈ Set.Ioc a b, ‖f s‖ ≤ B := fun s _ => by simpa [Real.norm_eq_abs] using hB s
  have h := norm_setIntegral_le_of_norm_le_const (by simp : volume (Set.Ioc a b) < ⊤) hnorm
  rwa [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hab] at h
