-- Prove2me | solution 1 for GeomDL.GroupConv.cyclic_cross_correlation
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:36:39.895175+00:00
-- url     : https://prove2.me/submissions/0b1d70d1-d787-4a7a-b3cc-d4a58fbcc137

import Mathlib
import Definitions.Def_GeomDL_GroupConv_Model

open GeomDL.GroupConv

theorem solution (n : ℕ) [NeZero n] (x θ : ZMod n → ℝ) (u : ZMod n) :
    groupConvolution (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod n)) x θ
      (CyclicShiftGroup.ofShift u) = ∑ v : ZMod n, x v * θ (v + u) := by
  unfold groupConvolution signalPairing signalAction
  rw [MeasureTheory.integral_fintype]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hs : ((CyclicShiftGroup.ofShift u)⁻¹ • v : ZMod n) = v + u := by
    show v - ((CyclicShiftGroup.ofShift u)⁻¹).toShift = v + u
    rw [show ((CyclicShiftGroup.ofShift u)⁻¹).toShift = -u from rfl, sub_neg_eq_add]
  simp [MeasureTheory.measureReal_def, hs]
  exact MeasureTheory.Integrable.of_finite
