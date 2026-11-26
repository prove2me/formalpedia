-- Prove2me | solution 1 for Kyprianou.Ch04.closedStopNestedIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:28:10.147112+00:00
-- url     : https://prove2.me/submissions/656b1f31-6b5a-4cf7-b843-b42bfa636788

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_closedStopMaskRegion
open MeasureTheory Filter Set Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- The closed stopped nested compensator integral equals the clipped-clock integral. -/
theorem solution (nu : Measure ℝ) (k : ℝ → ℝ → ℝ)
    (tau : WithTop NNReal) (t c : NNReal)
    (hc : (c : WithTop NNReal) = min tau (t : WithTop NNReal)) :
    (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x,
      (if (s.toNNReal : WithTop NNReal) ≤ tau then k s x else 0) ∂nu ∂volume) =
      ∫ s in Set.Icc (0 : ℝ) (c : ℝ), ∫ x, k s x ∂nu ∂volume := by
  classical
  let U := Set.Icc (0 : ℝ) (t : ℝ)
  let V := Set.Icc (0 : ℝ) (c : ℝ)
  have hU : MeasurableSet U := measurableSet_Icc
  have hV : MeasurableSet V := measurableSet_Icc
  have hVU : V ⊆ U := fun s hs => ((closedStopMaskRegion tau t c hc s).mpr hs).1
  have he : (fun s : ℝ => ∫ x, (if (s.toNNReal : WithTop NNReal) ≤ tau then k s x else 0) ∂nu)
      =ᵐ[volume.restrict U] V.indicator (fun s => ∫ x, k s x ∂nu) := by
    filter_upwards [ae_restrict_mem hU] with s hs
    have hh : (s.toNNReal : WithTop NNReal) ≤ tau ↔ s ∈ V := by
      change _ ↔ s ∈ Set.Icc (0 : ℝ) (c : ℝ)
      rw [← closedStopMaskRegion tau t c hc s]
      exact ⟨fun h => ⟨hs,h⟩,And.right⟩
    rw [Set.indicator_apply]
    by_cases h : (s.toNNReal : WithTop NNReal) ≤ tau
    · simp only [if_pos h,if_pos (hh.mp h)]
    · simp only [if_neg h,if_neg (fun hv => h (hh.mpr hv)),integral_zero]
  change (∫ s, _ ∂volume.restrict U) = ∫ s, (∫ x, k s x ∂nu) ∂volume.restrict V
  rw [integral_congr_ae he,integral_indicator hV,Measure.restrict_restrict_of_subset hVU]
