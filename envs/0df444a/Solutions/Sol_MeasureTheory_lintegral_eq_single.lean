-- Prove2me | solution 1 for MeasureTheory.lintegral_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T20:42:05.748213+00:00
-- url     : https://prove2.me/submissions/1cb42002-2d42-4d0e-8138-bbaac743d614

import Mathlib

set_option maxHeartbeats 800000
set_option autoImplicit false

open MeasureTheory ENNReal

theorem solution {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (a : α) (f : α → ℝ≥0∞) (ha : ∀ b ≠ a, f b = 0) :
    ∫⁻ x, f x ∂μ = f a * μ {a} := by
  have hf : f = Set.indicator {a} (fun _ => f a) := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp [Set.indicator_of_mem]
    · rw [ha b hb, Set.indicator_of_notMem]
      simpa using hb
  rw [hf, lintegral_indicator (measurableSet_singleton a), setLIntegral_const]
  simp [Set.indicator_of_mem]

#check @solution
