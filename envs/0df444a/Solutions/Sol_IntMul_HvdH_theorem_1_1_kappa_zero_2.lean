-- Prove2me | solution 2 for IntMul.HvdH.theorem_1_1_kappa_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T04:53:24.927071+00:00
-- url     : https://prove2.me/submissions/44bd4921-5a75-4af8-b4fb-3fad1e744cf4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_IntMul_Kappa_openai_theorem_1

open IntMul

theorem solution : KappaBound 0 := by
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
  exact mono _ _ (by norm_num) IntMul.Kappa.openai_theorem_1
