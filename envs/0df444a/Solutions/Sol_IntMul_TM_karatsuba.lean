-- Prove2me | solution 1 for IntMul.TM.karatsuba
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T17:33:53.512979+00:00
-- url     : https://prove2.me/submissions/96d65dd4-f7cf-4b58-8cc1-41be46121497
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_IntMul_TM_schonhage_strassen

open IntMul

theorem solution : MulTimeBound fun n => (n : ℝ) ^ Real.logb 2 3 := by
  -- `MulTimeBound` transfers along an eventual bound `g n ≤ C * h n`
  have mono : ∀ (g h : ℕ → ℝ) (C : ℝ) (n₁ : ℕ), 0 < C → (∀ n, n₁ ≤ n → g n ≤ C * h n) →
      MulTimeBound g → MulTimeBound h := by
    intro g h C n₁ hC hgh hg
    obtain ⟨M, hcorr, c, hc, n₀, hM⟩ := hg
    refine ⟨M, hcorr, c * C, mul_pos hc hC, max n₀ n₁, fun n hn h1 => ?_⟩
    intro x y hx hy
    obtain ⟨t, ht, hh⟩ := hM n (le_of_max_le_left hn) h1 x y hx hy
    refine ⟨t, ht.trans ?_, hh⟩
    have := hgh n (le_of_max_le_right hn)
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left this hc.le
  refine mono _ _ 16 3 (by norm_num) ?_ IntMul.TM.schonhage_strassen
  intro n hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  -- ln n > 1, since e < 3
  have hL1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hLL0 : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hL1.le
  have hLL : Real.log (Real.log n) ≤ Real.log n := Real.log_le_self (by linarith)
  -- ln n ≤ 4 n^{1/4}
  have hL4 : Real.log n ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have := Real.log_le_rpow_div hn0 (by norm_num : (0 : ℝ) < 1 / 4)
    have e : (n : ℝ) ^ ((1 : ℝ) / 4) / (1 / 4) = 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by ring
    linarith
  have hq0 : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hn0 _
  -- n · n^{1/4} · n^{1/4} = n^{3/2}
  have hpow : (n : ℝ) * ((n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4)) =
      (n : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_add (by linarith), show (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 + 1 / 4) =
      (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 + 1 / 4) by rw [Real.rpow_one],
      ← Real.rpow_add (by linarith)]
    norm_num
  -- 3/2 ≤ log₂ 3, since 2^{3/2} = √8 ≤ 3
  have hexp : (3 : ℝ) / 2 ≤ Real.logb 2 3 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    have h8 : (2 : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt 8 := by
      rw [Real.sqrt_eq_rpow, show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h8, Real.sqrt_le_left (by norm_num)]; norm_num
  have hmono : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ Real.logb 2 3 :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
  calc (n : ℝ) * Real.log n * Real.log (Real.log n)
      ≤ (n : ℝ) * (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) := by
        gcongr
        all_goals linarith [hLL.trans hL4]
    _ = 16 * ((n : ℝ) * ((n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4))) := by ring
    _ = 16 * (n : ℝ) ^ ((3 : ℝ) / 2) := by rw [hpow]
    _ ≤ 16 * (n : ℝ) ^ Real.logb 2 3 := by gcongr
