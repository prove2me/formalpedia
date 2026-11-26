-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SmoothJoinValueV11
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:46:31.719151+00:00
-- url     : https://prove2.me/submissions/dbdf2454-a396-4f35-bddf-2a9ec56cdec3

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (fLeft fRight : ℝ → ℝ)
    (hL : ContDiff ℝ 1 fLeft) (hR : ContDiff ℝ 1 fRight)
    (p : ℕ → ℝ → ℝ)
    (hP : ∀ x, Tendsto (fun n => p n x) atTop (𝓝 (max 0 x)))
    (x : ℝ) :
    let g := fun n (x : ℝ) => fLeft (-p n (-x)) - fLeft 0 +
      fRight (p n x) - fRight 0
    Tendsto (fun n => g n x) atTop (𝓝
      (if x < 0 then fLeft x - fLeft 0
       else if 0 < x then fRight x - fRight 0 else 0)) := by
  have h1 := hL.continuous.continuousAt.tendsto.comp ((hP (-x)).neg)
  have h2 := hR.continuous.continuousAt.tendsto.comp (hP x)
  have h := ((h1.sub (tendsto_const_nhds (x := fLeft 0))).add h2).sub
    (tendsto_const_nhds (x := fRight 0))
  change Tendsto (fun n => fLeft (-p n (-x)) - fLeft 0 + fRight (p n x) - fRight 0)
    atTop _
  by_cases hx : x < 0
  · have hnx : 0 ≤ -x := by linarith
    simpa [Function.comp_def, hx, max_eq_left hx.le, max_eq_right hnx] using h
  · by_cases hp : 0 < x
    · have hnx : -x ≤ 0 := by linarith
      simpa [Function.comp_def, hx, hp, max_eq_right hp.le, max_eq_left hnx] using h
    · have hz : x = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hx)
      simpa [Function.comp_def, hz, sub_self] using h
