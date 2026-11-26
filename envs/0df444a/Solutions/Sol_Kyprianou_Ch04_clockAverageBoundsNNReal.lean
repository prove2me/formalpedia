-- Prove2me | solution 1 for Kyprianou.Ch04.clockAverageBoundsNNReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:32:09.229895+00:00
-- url     : https://prove2.me/submissions/cb028554-9ecb-4c1d-bd39-c798fc485a0a

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (mu : Measure NNReal) [IsProbabilityMeasure mu]
    (f : NNReal → ℝ) (ell : ℝ)
    (hf : Integrable f mu) (hanti : Antitone f)
    (hlow : ∀ t, ell ≤ f t) (h0 : ∀ t, 0 ≤ f t)
    (h1 : ∀ t, f t ≤ 1) (T : NNReal) :
    ell ≤ (∫ t, f t ∂mu) ∧
      (∫ t, f t ∂mu) ≤ f T + (mu (Iio T)).toReal := by
  constructor
  · have h := integral_mono (integrable_const ell) hf hlow
    simpa using h
  · let g : NNReal → ℝ := (Iio T).indicator (fun _ => 1)
    have hg : Integrable g mu :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Iio
    have hgi : (∫ t, g t ∂mu) = (mu (Iio T)).toReal := by
      rw [show g = (Iio T).indicator (fun _ => (1 : ℝ)) from rfl,
        integral_indicator measurableSet_Iio, integral_const]
      simp [Measure.real]
    have hle : f ≤ fun t => f T + g t := by
      intro t
      by_cases ht : t < T
      · have ht' : t ∈ Iio T := ht
        change f t ≤ f T + (Iio T).indicator (fun _ => (1 : ℝ)) t
        rw [indicator_of_mem ht']
        linarith [h1 t, h0 T]
      · change f t ≤ f T + (Iio T).indicator (fun _ => (1 : ℝ)) t
        rw [indicator_of_notMem (show t ∉ Iio T from ht), add_zero]
        exact hanti (le_of_not_gt ht)
    calc
      _ ≤ ∫ t, f T + g t ∂mu :=
        integral_mono hf ((integrable_const (f T)).add hg) hle
      _ = _ := by rw [integral_add (integrable_const _) hg, hgi]; simp
