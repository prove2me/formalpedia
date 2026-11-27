-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45BadLeftPathV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:10:55.614803+00:00
-- url     : https://prove2.me/submissions/6096959d-30de-4a7c-b0e8-9aaca6a8810b

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The altered left state has the correct positive-time limits and zero jump measure. -/
theorem solution {m : MeasurableSpace ℕ} (P : @Measure ℕ m) :
    let X : NNReal → ℕ → ℝ := fun t _ => (t : ℝ)
    let Y : NNReal → ℕ → ℝ := fun t w => if t = 0 then (w : ℝ) else (t : ℝ)
    (∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Y t w))) ∧
    (∀ w, Kyprianou.Ch04.pathJumpMeasure X Y w = 0) := by
  let X : NNReal → ℕ → ℝ := fun t _ => (t : ℝ)
  let Y : NNReal → ℕ → ℝ := fun t w => if t = 0 then (w : ℝ) else (t : ℝ)
  refine ⟨?_,?_⟩
  · filter_upwards [] with w
    intro t ht
    simpa only [X,Y,if_neg ht.ne'] using
      (NNReal.continuous_coe.continuousWithinAt :
        ContinuousWithinAt (fun s : NNReal => (s : ℝ)) (Iio t) t).tendsto
  · intro w
    change Kyprianou.Ch04.pathJumpMeasure X Y w = 0
    have hS : {t : NNReal | 0 < t ∧ X t w ≠ Y t w} = ∅ := by
      ext t
      simp only [mem_setOf_eq,mem_empty_iff_false,iff_false,not_and]
      intro ht
      simp [X,Y,ht.ne']
    unfold Kyprianou.Ch04.pathJumpMeasure
    rw [hS]
    simp
