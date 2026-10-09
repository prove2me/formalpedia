-- Prove2me | solution 1 for IntMul.Kappa.colkitt_2pow30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T04:49:46.623881+00:00
-- url     : https://prove2.me/submissions/e6923bc8-9eec-4c24-8712-94610475c80a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_IntMul_Kappa_jain_round6

open IntMul

theorem solution : KappaBound (1 / 2 ^ 30) := by
  -- `KappaBound` is antitone in κ: `lg n ≥ 1`, so `(lg n)^(1-κ)` decreases as κ grows.
  have mono : ∀ κ κ' : ℝ, κ' ≤ κ → KappaBound κ → KappaBound κ' := by
    intro κ κ' hk h
    obtain ⟨M, hcorr, c, hc, n₀, hM⟩ := h
    refine ⟨M, hcorr, c, hc, n₀, fun n hn h1 => ?_⟩
    intro x y hx hy
    obtain ⟨t, ht, hh⟩ := hM n hn h1 x y hx hy
    refine ⟨t, ht.trans ?_, hh⟩
    have hlg : (1 : ℝ) ≤ (lg n : ℝ) := by exact_mod_cast le_max_right _ _
    have hpow : (lg n : ℝ) ^ (1 - κ) ≤ (lg n : ℝ) ^ (1 - κ') :=
      Real.rpow_le_rpow_of_exponent_le hlg (by linarith)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)) hc.le
  exact mono _ _ (by norm_num) IntMul.Kappa.jain_round6
