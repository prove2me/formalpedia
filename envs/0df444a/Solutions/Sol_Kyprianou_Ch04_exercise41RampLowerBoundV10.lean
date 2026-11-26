-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41RampLowerBoundV10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:43:30.622629+00:00
-- url     : https://prove2.me/submissions/5c4240c0-8a6a-4853-b5e3-0c7feda08d49

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false
theorem solution
    (ε : ℝ) (he : 0 < ε) (x : ℝ) (hx : ε ≤ x) :
    let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
    let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
    x - ε ≤ p x := by
  let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
  let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hr0 (u : ℝ) : 0 ≤ r u := le_min (by norm_num) (le_max_left _ _)
  have htail : (∫ u in ε..x, r u) = x - ε := by
    calc
      _ = ∫ _ in ε..x, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hx]
        intro u hu
        have hd : 1 ≤ u / ε := (le_div_iff₀ he).mpr (by simpa using hu.1)
        exact min_eq_left (hd.trans (le_max_right _ _))
      _ = x - ε := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hr.intervalIntegrable 0 ε) (hr.intervalIntegrable ε x)
  have hnon := intervalIntegral.integral_nonneg_of_forall (μ := volume) he.le hr0
  change x - ε ≤ ∫ u in (0 : ℝ)..x, r u
  rw [← hadd, htail]
  linarith
