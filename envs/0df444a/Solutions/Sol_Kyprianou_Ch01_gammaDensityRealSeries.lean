-- Prove2me | solution 1 for Kyprianou.Ch01.gammaDensityRealSeries
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:15:54.233167+00:00
-- url     : https://prove2.me/submissions/77af6709-e5e6-4397-a2a4-b98acac3c2b1

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real NormedSpace Filter
open scoped BigOperators
set_option autoImplicit false

theorem solution
    (beta x : ℝ) (hbeta : 0 < beta) (hx : 0 ≤ x) :
    (∑' n : ℕ, beta ^ (n + 1) * x ^ n *
      Real.exp (-beta * x) / (n.factorial : ℝ)) = beta := by
  have hsum : (∑' n : ℕ, (beta * x) ^ n / (n.factorial : ℝ)) =
      Real.exp (beta * x) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    apply tsum_congr
    intro n
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  have hs : Summable (fun n : ℕ => (beta * x) ^ n / (n.factorial : ℝ)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (expSeries_summable' (𝕂 := ℝ) (beta * x))
  calc
    (∑' n : ℕ, beta ^ (n + 1) * x ^ n *
      Real.exp (-beta * x) / (n.factorial : ℝ)) =
        ∑' n : ℕ, (beta * Real.exp (-beta * x)) *
          ((beta * x) ^ n / (n.factorial : ℝ)) := by
            apply tsum_congr
            intro n
            rw [pow_succ, mul_pow]
            ring
    _ = (beta * Real.exp (-beta * x)) *
          (∑' n : ℕ, (beta * x) ^ n / (n.factorial : ℝ)) := by
            exact hs.tsum_mul_left _
    _ = beta := by
      rw [hsum]
      rw [mul_assoc, ← Real.exp_add]
      have hz : -beta * x + beta * x = 0 := by ring
      simp [hz]
