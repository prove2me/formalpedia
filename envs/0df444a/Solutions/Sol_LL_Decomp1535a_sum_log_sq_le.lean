-- Prove2me | solution 1 for LL_Decomp1535a.sum_log_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:04:59.51495+00:00
-- url     : https://prove2.me/submissions/fcecf5fb-1096-442f-80a4-45770f0f8aec

import Mathlib
import Definitions.Def_LL_Decomp1535a_theta

open MeasureTheory

noncomputable def GbAAux.thetaA (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p

theorem GbAAux.sum_log_sq_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 ≤
      Real.log N * GbAAux.thetaA N := by
  unfold GbAAux.thetaA
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := Finset.mem_filter.1 hp
  have hpN : p ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp'.1)
  have h0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h2 : Real.log p ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hpN)
  nlinarith

theorem solution (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 ≤
      Real.log N * LL_Decomp1535a.theta N :=
  GbAAux.sum_log_sq_le N
