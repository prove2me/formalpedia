-- Prove2me | solution 1 for Kyprianou.Ch04.atomicMeasureSingularV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:29:22.316307+00:00
-- url     : https://prove2.me/submissions/185669be-13fb-431a-96fc-9f8179f4db45

import Mathlib
open MeasureTheory Set Function
open scoped ENNReal
set_option autoImplicit false

/-- A weighted countably supported sum of point masses is singular to Lebesgue measure. -/
theorem solution {ι : Type} (a : ι → ℝ) (w : ι → ℝ)
    (hw : Summable w) :
    (Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (a i))).MutuallySingular
      (volume : Measure ℝ) := by
  classical
  let S := a '' Function.support w
  have hc : S.Countable := hw.countable_support.image a
  refine ⟨Sᶜ, hc.measurableSet.compl, ?_, ?_⟩
  · rw [Measure.sum_apply _ hc.measurableSet.compl]
    apply ENNReal.tsum_eq_zero.mpr
    intro i
    rw [Measure.smul_apply]
    by_cases hi : w i = 0
    · simp [hi]
    · have hm : a i ∈ S := ⟨i, hi, rfl⟩
      simp [Measure.dirac_apply' _ hc.measurableSet.compl, hm]
  · simpa using hc.measure_zero (μ := (volume : Measure ℝ))
