-- Prove2me | solution 1 for IntMul.TM.schoolbook
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T17:37:29.808451+00:00
-- url     : https://prove2.me/submissions/0b9fc29d-1182-4c18-badd-c2e9cec9632a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_IntMul_TM_karatsuba

open IntMul

theorem solution : MulTimeBound fun n => (n : ℝ) ^ 2 := by
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
  refine mono _ _ 1 1 one_pos ?_ IntMul.TM.karatsuba
  intro n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- log₂ 3 ≤ 2, since 3 ≤ 4
  have hexp : Real.logb 2 3 ≤ 2 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num
  have := Real.rpow_le_rpow_of_exponent_le hnR hexp
  rw [Real.rpow_two] at this
  simpa using this
