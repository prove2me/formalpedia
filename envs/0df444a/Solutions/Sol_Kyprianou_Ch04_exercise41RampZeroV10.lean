-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41RampZeroV10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:40:47.3988+00:00
-- url     : https://prove2.me/submissions/4cf9a836-6ded-42e1-a01b-4f47c5a5ef20

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false
theorem solution
    (ε : ℝ) (he : 0 < ε) (x : ℝ) (hx : x ≤ 0) :
    let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
    let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
    p x = 0 := by
  let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
  let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
  change (∫ u in (0 : ℝ)..x, r u) = 0
  rw [intervalIntegral.integral_symm]
  have h : (∫ u in x..(0 : ℝ), r u) = ∫ _ in x..(0 : ℝ), (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hx]
    intro u hu
    have hh : u / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu.2 he.le
    simp [r, max_eq_left hh]
  rw [h]
  simp
