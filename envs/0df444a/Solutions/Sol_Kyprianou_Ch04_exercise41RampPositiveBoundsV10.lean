-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41RampPositiveBoundsV10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:43:30.488778+00:00
-- url     : https://prove2.me/submissions/50dcea25-a79d-464b-a2ed-5312a46ac7e6

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false
theorem solution
    (ε : ℝ) (x : ℝ) (hx : 0 ≤ x) :
    let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
    let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
    0 ≤ p x ∧ p x ≤ x := by
  let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
  let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hr0 (u : ℝ) : 0 ≤ r u := le_min (by norm_num) (le_max_left _ _)
  have hr1 (u : ℝ) : r u ≤ 1 := min_le_left _ _
  refine ⟨intervalIntegral.integral_nonneg_of_forall hx hr0, ?_⟩
  have h := intervalIntegral.integral_mono_on (μ := volume) hx
    (hr.intervalIntegrable 0 x) (continuous_const.intervalIntegrable 0 x)
    (fun u _ => hr1 u)
  simpa [p] using h
