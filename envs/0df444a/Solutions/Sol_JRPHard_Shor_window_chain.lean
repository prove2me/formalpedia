-- Prove2me | solution 1 for JRPHard.Shor.window_chain
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:13:16.194987+00:00
-- url     : https://prove2.me/submissions/ecfc4a3e-d917-4760-81c2-06f8bfdb7513

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (hn : 0 < n) (b c lam P : ℝ)
    (hlam0 : 0 < lam) (hlam : lam ≤ 2 * (n : ℝ))
    (hc : c * b < lam * (2 : ℝ) ^ (b / 2) / (4 * (n : ℝ)))
    (hwin : (2 : ℝ) ^ b - c * b * (2 : ℝ) ^ (b / 2) < P ∧
      P < (2 : ℝ) ^ b + c * b * (2 : ℝ) ^ (b / 2)) :
    ((2 : ℝ) ^ b * (1 - lam / (4 * (n : ℝ))) < P ∧
      P < (2 : ℝ) ^ b * (1 + lam / (4 * (n : ℝ)))) ∧
    ((2 : ℝ) ^ b * (2 : ℝ) ^ (-(lam / (2 * (n : ℝ)))) < P ∧
      P < (2 : ℝ) ^ b * (2 : ℝ) ^ (lam / (2 * (n : ℝ)))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set A : ℝ := (2 : ℝ) ^ b with hA
  have hApos : 0 < A := by positivity
  have hh : (0 : ℝ) < (2 : ℝ) ^ (b / 2) := by positivity
  have hAA : (2 : ℝ) ^ (b / 2) * (2 : ℝ) ^ (b / 2) = A := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring
  -- key: c b 2^(b/2) < A * (lam/(4n))
  have key : c * b * (2 : ℝ) ^ (b / 2) < A * (lam / (4 * (n : ℝ))) := by
    have := mul_lt_mul_of_pos_right hc hh
    calc c * b * (2 : ℝ) ^ (b / 2) < lam * (2 : ℝ) ^ (b / 2) / (4 * (n : ℝ)) * (2 : ℝ) ^ (b / 2) := this
      _ = A * (lam / (4 * (n : ℝ))) := by rw [← hAA]; ring
  set x : ℝ := lam / (2 * (n : ℝ)) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one (by positivity)]; exact hlam
  have hx4 : lam / (4 * (n : ℝ)) = x / 2 := by rw [hx]; field_simp; ring
  rw [hx4] at key ⊢
  obtain ⟨h1, h2⟩ := hwin
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2b : (1/2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have e1 : (2 : ℝ) ^ (-x) ≤ 1 - x / 2 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    have hconv := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-Real.log 2))
      (show (0:ℝ) ≤ 1 - x by linarith) (show (0:ℝ) ≤ x by linarith) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)] at hconv
    have : Real.log 2 * -x = x * -Real.log 2 := by ring
    rw [this]
    nlinarith [hconv]
  have e2 : 1 + x / 2 ≤ (2 : ℝ) ^ x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    have := Real.add_one_le_exp (Real.log 2 * x)
    nlinarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have : A * (2:ℝ) ^ (-x) ≤ A * (1 - x / 2) := mul_le_mul_of_nonneg_left e1 hApos.le
    nlinarith
  · have : A * (1 + x / 2) ≤ A * (2:ℝ) ^ x := mul_le_mul_of_nonneg_left e2 hApos.le
    nlinarith
