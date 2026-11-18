-- Prove2me | solution 1 for Kyprianou.ProofPreparation.integrable_small_part_of_integrable_truncated
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:05:48.03869+00:00
-- url     : https://prove2.me/submissions/ac817d61-06af-4573-a1c7-d34568390cd9

import Mathlib
open MeasureTheory
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E] (m : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (htrunc : Integrable (fun x => min (1 : ℝ) |f x|) m) :
    Integrable (fun x => if |f x| ≤ 1 then f x else 0) m := by
  refine htrunc.mono' ?_ ?_
  · exact (Measurable.ite (measurableSet_le (hf.abs) measurable_const) hf measurable_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    split_ifs with h
    · rw [Real.norm_eq_abs]; exact le_min h le_rfl
    · simp [le_min_iff, abs_nonneg]
