-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.measurable_set_fiber_fubini_real
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:14:01.969289+00:00
-- url     : https://prove2.me/submissions/d0b1eec3-1129-489e-a12c-2469c8835474

import Mathlib

open MeasureTheory
open scoped BigOperators

namespace PXSl

lemma slice (m : ℕ) (s : Set (Fin (m + 1) → ℝ)) (hs : MeasurableSet s) :
    volume s = ∫⁻ t, volume {y : Fin m → ℝ | Fin.cons t y ∈ s} := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
  have hs' : MeasurableSet ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm ⁻¹' s) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm.measurable hs
  rw [← hp.measure_preimage hs.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_apply hs']
  refine lintegral_congr (fun t => ?_)
  congr 1
  ext y
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

lemma slice_meas (m : ℕ) (s : Set (Fin (m + 1) → ℝ)) (hs : MeasurableSet s) :
    Measurable (fun t : ℝ => volume {y : Fin m → ℝ | Fin.cons t y ∈ s}) := by
  have hs' : MeasurableSet ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm ⁻¹' s) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm.measurable hs
  have := measurable_measure_prodMk_left (ν := (volume : Measure (Fin m → ℝ))) hs'
  convert this using 2 with t
  congr 1
  ext y
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

end PXSl


open Filter Topology in
theorem solution (m : Nat) (s : Set (Fin (m + 1) → Real)) (hs : MeasurableSet s) (hfinite : MeasureTheory.volume s ≠ ⊤) : (MeasureTheory.Integrable (fun t : Real => (MeasureTheory.volume {y : Fin m → Real | Fin.cons t y ∈ s}).toReal) MeasureTheory.volume) ∧ (MeasureTheory.integral MeasureTheory.volume (fun t : Real => (MeasureTheory.volume {y : Fin m → Real | Fin.cons t y ∈ s}).toReal) = (MeasureTheory.volume s).toReal) := by
  have hm := PXSl.slice_meas m s hs
  have hl : ∫⁻ t, volume {y : Fin m → ℝ | Fin.cons t y ∈ s} ≠ ⊤ := by
    rw [← PXSl.slice m s hs]; exact hfinite
  refine ⟨integrable_toReal_of_lintegral_ne_top hm.aemeasurable hl, ?_⟩
  rw [integral_toReal hm.aemeasurable (ae_lt_top hm hl), ← PXSl.slice m s hs]
