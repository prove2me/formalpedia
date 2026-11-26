-- Prove2me | solution 1 for Kyprianou.Ch04.closedStopRawIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:28:10.237949+00:00
-- url     : https://prove2.me/submissions/793a921a-9c92-4472-8b4f-53a6206fcb33

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_closedStopMaskRegion
open MeasureTheory Filter Set Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- The physical stopped raw integral equals the integral at the clipped clock. -/
theorem solution (mu : Measure (ℝ × ℝ)) (k : ℝ × ℝ → ℝ)
    (tau : WithTop NNReal) (t c : NNReal)
    (hc : (c : WithTop NNReal) = min tau (t : WithTop NNReal)) :
    (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      (if (z.1.toNNReal : WithTop NNReal) ≤ tau then k z else 0) ∂mu) =
      ∫ z in Set.Icc (0 : ℝ) (c : ℝ) ×ˢ Set.univ, k z ∂mu := by
  classical
  let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
  let V := Set.Icc (0 : ℝ) (c : ℝ) ×ˢ (Set.univ : Set ℝ)
  have hU : MeasurableSet U := measurableSet_Icc.prod MeasurableSet.univ
  have hV : MeasurableSet V := measurableSet_Icc.prod MeasurableSet.univ
  have hVU : V ⊆ U := fun z hz =>
    ⟨((closedStopMaskRegion tau t c hc z.1).mpr hz.1).1,hz.2⟩
  have he : (fun z : ℝ × ℝ => if (z.1.toNNReal : WithTop NNReal) ≤ tau then k z else 0)
      =ᵐ[mu.restrict U] V.indicator k := by
    filter_upwards [ae_restrict_mem hU] with z hz
    rw [Set.indicator_apply]
    have hz' : (z.1.toNNReal : WithTop NNReal) ≤ tau ↔ z ∈ V := by
      change _ ↔ z.1 ∈ Set.Icc (0 : ℝ) (c : ℝ) ∧ z.2 ∈ (Set.univ : Set ℝ)
      simp only [Set.mem_univ,and_true]
      rw [← closedStopMaskRegion tau t c hc z.1]
      exact ⟨fun h => ⟨hz.1,h⟩,And.right⟩
    by_cases hs : (z.1.toNNReal : WithTop NNReal) ≤ tau
    · rw [if_pos hs,if_pos (hz'.mp hs)]
    · rw [if_neg hs,if_neg (fun hv => hs (hz'.mpr hv))]
  change (∫ z, _ ∂mu.restrict U) = ∫ z, k z ∂mu.restrict V
  rw [integral_congr_ae he,integral_indicator hV,Measure.restrict_restrict_of_subset hVU]
