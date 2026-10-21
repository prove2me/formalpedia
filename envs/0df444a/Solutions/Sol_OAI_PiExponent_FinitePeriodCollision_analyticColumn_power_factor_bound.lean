-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.analyticColumn_power_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:43:53.876878+00:00
-- url     : https://prove2.me/submissions/923ab5b1-b4ac-42e0-8e3b-8673a1fa96ca

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (a A : Fin m → ℕ) {R : ℝ} (z : ℂ)
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖z ^ (∑ i, (a i - A i))‖ ≤
      Real.exp ((∑ i, (a i : ℝ)) * Real.log R) := by
  let n : ℕ := ∑ i, (a i - A i)
  let N : ℕ := ∑ i, a i
  have hn : n ≤ N := by
    dsimp [n, N]
    exact Finset.sum_le_sum fun i hi => Nat.sub_le (a i) (A i)
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  calc
    ‖z ^ n‖ = ‖z‖ ^ n := norm_pow z n
    _ ≤ R ^ n := by
      exact pow_le_pow_left₀ (norm_nonneg z) hz n
    _ ≤ R ^ N := pow_le_pow_right₀ hR hn
    _ = (Real.exp (Real.log R)) ^ N := by
      rw [Real.exp_log hRpos]
    _ = Real.exp ((N : ℝ) * Real.log R) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp ((∑ i, (a i : ℝ)) * Real.log R) := by
      simp [N, Nat.cast_sum]