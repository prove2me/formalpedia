-- Prove2me | solution 1 for Kyprianou.Ch04.atomicMeasureMassV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:31:45.41584+00:00
-- url     : https://prove2.me/submissions/3e21d1e9-8b0b-4b85-b5f0-eafe25a5815a

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

/-- Mass on a measurable set for an absolutely summable nonnegative atomic measure. -/
theorem solution {ι : Type} (a : ι → ℝ) (w : ι → ℝ)
    (hw : Summable w) (hn : ∀ i, 0 ≤ w i)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (a i))) S =
      ENNReal.ofReal (∑' i, (a ⁻¹' S).indicator w i) := by
  classical
  have hsum : Summable (fun i => if a i ∈ S then w i else 0) :=
    Summable.of_nonneg_of_le (fun i => by split <;> simp_all)
      (fun i => by split <;> simp_all) hw
  change _ = ENNReal.ofReal (∑' i, if a i ∈ S then w i else 0)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => by split <;> simp_all) hsum,
    Measure.sum_apply _ hS]
  congr 1
  funext i
  by_cases hi : a i ∈ S <;> simp [Measure.smul_apply, Measure.dirac_apply' _ hS, hi]
