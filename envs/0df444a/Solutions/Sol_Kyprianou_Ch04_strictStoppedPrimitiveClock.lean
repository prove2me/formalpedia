-- Prove2me | solution 1 for Kyprianou.Ch04.strictStoppedPrimitiveClock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:47:50.574196+00:00
-- url     : https://prove2.me/submissions/18a84ede-682a-4ad9-a672-fd899a28d8f3

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_closedStopMaskRegion
open MeasureTheory Filter Set Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- Strict stopping of a Lebesgue density agrees with the closed clipped clock. -/
theorem solution (g : ℝ → ℝ) (tau : WithTop NNReal) (t c : NNReal)
    (hc : (c : WithTop NNReal) = min tau (t : WithTop NNReal)) :
    (∫ s in Icc (0:ℝ) (t:ℝ), (if (s.toNNReal : WithTop NNReal) < tau then g s else 0) ∂volume)
      = ∫ s in Icc (0:ℝ) (c:ℝ), g s ∂volume := by
  classical
  let U := Icc (0:ℝ) (t:ℝ)
  let V := Icc (0:ℝ) (c:ℝ)
  have hVU : V ⊆ U := fun s hs => ((closedStopMaskRegion tau t c hc s).mpr hs).1
  have he : (fun s : ℝ => if (s.toNNReal : WithTop NNReal) < tau then g s else 0)
      =ᵐ[volume.restrict U] V.indicator g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae ((Set.countable_singleton (c:ℝ)).ae_notMem volume)] with s hs hne
    have heq : (s.toNNReal : WithTop NNReal) < tau ↔ s ∈ V := by
      constructor
      · intro h
        exact (closedStopMaskRegion tau t c hc s).mp ⟨hs,h.le⟩
      · intro hv
        have h := ((closedStopMaskRegion tau t c hc s).mpr hv).2
        refine lt_of_le_of_ne h (fun he => hne ?_)
        have hsc : (s.toNNReal : WithTop NNReal) = (c : WithTop NNReal) := by
          rw [hc,← he,min_eq_left (WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hs.2))]
        exact WithTop.coe_injective hsc ▸ (Real.coe_toNNReal _ hs.1).symm
    simp only [Set.indicator_apply,heq]
  change (∫ s, _ ∂volume.restrict U) = ∫ s, g s ∂volume.restrict V
  rw [integral_congr_ae he,integral_indicator measurableSet_Icc,Measure.restrict_restrict_of_subset hVU]
