-- Prove2me | solution 1 for IntMul.HvdH.theorem_1_1_kappa_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T00:47:19.929028+00:00
-- url     : https://prove2.me/submissions/1aae896c-f796-4e85-8890-a1b56be76887
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_IntMul_HvdH_theorem_1_1

open IntMul

theorem solution : KappaBound 0 := by
  obtain ⟨M, hcorr, c, hc, n₀, hM⟩ := IntMul.HvdH.theorem_1_1
  refine ⟨M, hcorr, c, hc, n₀, fun n hn h1n => ?_⟩
  -- ln n ≤ ⌈log₂ n⌉ · ln 2 ≤ lg n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hlog : Real.log n ≤ (lg n : ℝ) := by
    have h1 : ((n : ℕ) : ℝ) ≤ ((2 ^ Nat.clog 2 n : ℕ) : ℝ) :=
      by exact_mod_cast Nat.le_pow_clog (by norm_num) n
    have h2 := Real.log_le_log (by linarith) h1
    push_cast at h2
    rw [Real.log_pow] at h2
    have hl2 := Real.log_two_lt_d9
    have h3 : ((Nat.clog 2 n : ℕ) : ℝ) ≤ (lg n : ℝ) := by
      exact_mod_cast le_max_left _ _
    have h4 : ((Nat.clog 2 n : ℕ) : ℝ) * Real.log 2 ≤ (Nat.clog 2 n : ℝ) :=
      mul_le_of_le_one_right (Nat.cast_nonneg _) (by linarith)
    linarith
  intro x y hx hy
  obtain ⟨t, ht, hh⟩ := hM n hn h1n x y hx hy
  refine ⟨t, ht.trans ?_, hh⟩
  simp only [sub_zero, Real.rpow_one]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by linarith)) hc.le
