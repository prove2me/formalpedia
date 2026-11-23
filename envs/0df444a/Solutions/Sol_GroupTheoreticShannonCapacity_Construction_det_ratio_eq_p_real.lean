-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.det_ratio_eq_p_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:55.854443+00:00
-- url     : https://prove2.me/submissions/6f880184-6d49-4562-a1d8-4a1114678cd6

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
section
namespace GroupTheoreticShannonCapacity.Construction
open Matrix
private lemma neg_one_pow_ne_zero (n : ℕ) : (-1 : ℝ)^n ≠ 0 := by
  rcases neg_one_pow_eq_or ℝ n with hp | hp <;> simp [hp]
section Tests
example : a 2 1 2 1 0 = 5 := by decide
example : p 2 1 2 1 0 = 5 := by
  simp only [p, a]
  norm_num
example : q 2 1 2 1 0 = 2 := by
  simp only [q, a]
  norm_num
example : p 2 1 2 1 0 = q 2 1 2 1 0 * 0 + 1 * (a 2 1 2 1 0)^(2-1) := by
  simp only [p, q, a]
  norm_num
example : p 2 1 2 1 0 * 2 = q 2 1 2 1 0 * (a 2 1 2 1 0) - 1 * 0^(2-1) := by
  simp only [p, q, a]
  norm_num
end Tests
end GroupTheoreticShannonCapacity.Construction
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r s : ℤ) (hd : r + k * b ^ n ≠ 0) (hk : k ≠ 0) :
    let α : ℝ := (r : ℝ) / (k : ℝ)
    ((-s : ℝ)^n * α + (-a n k b r s : ℝ)^n) / ((-1 : ℝ)^n * α + (-b : ℝ)^n) =
    (p n k b r s : ℝ) := by
  intro α
  have h_num : (-s : ℝ)^n * α + (-a n k b r s : ℝ)^n =
      (-1 : ℝ)^n * ((s : ℝ)^n * α + (a n k b r s : ℝ)^n) := by rw [neg_pow, neg_pow]; ring
  have h_denom : (-1 : ℝ)^n * α + (-b : ℝ)^n = (-1 : ℝ)^n * (α + (b : ℝ)^n) := by rw [neg_pow]; ring
  rw [h_num, h_denom]
  have h_pow_ne := neg_one_pow_ne_zero n
  rw [mul_div_mul_left _ _ h_pow_ne]
  simp only [α]
  have hk_real : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hd_real : (r : ℝ) + (k : ℝ) * (b : ℝ) ^ n ≠ 0 := by exact_mod_cast hd
  have hdenom_ne : (r : ℝ) / (k : ℝ) + (b : ℝ) ^ n ≠ 0 := by
    rw [ne_eq, add_eq_zero_iff_eq_neg, div_eq_iff hk_real]
    intro h; exact hd_real (by linarith)
  simp only [p]; push_cast; field_simp [hk_real, hd_real, hdenom_ne]
end GroupTheoreticShannonCapacity.Construction
