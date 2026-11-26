-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SmoothJoinDerivLimitV11
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:46:31.705784+00:00
-- url     : https://prove2.me/submissions/be6bb5a8-0dec-445e-9544-c0e8787d56cc

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (fLeft fRight : ℝ → ℝ)
    (hL : ContDiff ℝ 1 fLeft) (hR : ContDiff ℝ 1 fRight)
    (p : ℕ → ℝ → ℝ)
    (hP : ∀ x, Tendsto (fun n => p n x) atTop (𝓝 (max 0 x)))
    (hD : ∀ x, Tendsto (fun n => deriv (p n) x) atTop
      (𝓝 (if 0 < x then 1 else 0)))
    (x : ℝ) :
    Tendsto (fun n => deriv fLeft (-p n (-x)) * deriv (p n) (-x) +
      deriv fRight (p n x) * deriv (p n) x) atTop (𝓝
      (if x < 0 then deriv fLeft x else if 0 < x then deriv fRight x else 0)) := by
  have h1 := hL.continuous_deriv_one.continuousAt.tendsto.comp ((hP (-x)).neg)
  have h2 := hR.continuous_deriv_one.continuousAt.tendsto.comp (hP x)
  have h := (h1.mul (hD (-x))).add (h2.mul (hD x))
  by_cases hx : x < 0
  · have hnx : 0 < -x := by linarith
    have hpx : ¬ 0 < x := not_lt_of_ge hx.le
    simpa [Function.comp_def, hx, hpx, hnx, max_eq_left hx.le, max_eq_right hnx.le] using h
  · by_cases hp : 0 < x
    · have hnx : -x ≤ 0 := by linarith
      have hn : ¬ 0 < -x := not_lt_of_ge hnx
      simpa [Function.comp_def, hx, hp, hn, max_eq_right hp.le, max_eq_left hnx] using h
    · have hz : x = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hx)
      simpa [Function.comp_def, hz] using h
