-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.p_over_q_le_a_over_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:03.333335+00:00
-- url     : https://prove2.me/submissions/d5fb2edf-2dbe-4871-ad03-ef3e80bfcb04

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_pb_eq_qa_minus

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n) (hk : 0 < k) (hb : 0 < b)
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    p n k b r s / q n k b r s ≤ a n k b r s / b := by
  -- First show the denominator r + k*b^n is positive (needed for pb_eq_qa_minus)
  have hd_pos : 0 < r + k * b^n := by
    have hbn : 0 < b^n := pow_pos hb n
    have hkbn : 0 < k * b^n := mul_pos hk hbn
    linarith
  have hd : r + k * b^n ≠ 0 := ne_of_gt hd_pos
  -- Use claim (ii): pb = qa - rs^{n-1}, so p/q = a/b - rs^{n-1}/(bq)
  have h_pb := pb_eq_qa_minus n k b r s hn hd
  -- Show a > 0
  have ha_pos : 0 < a n k b r s := by
    simp only [a]
    have hbn : 0 < b^n := pow_pos hb n
    have hkbn : 0 < k * b^n := mul_pos hk hbn
    have hsb : 0 ≤ s * b := mul_nonneg hs (le_of_lt hb)
    linarith
  -- Need q > 0 for division
  have hq_pos : 0 < q n k b r s := by
    simp only [q]
    have hd_pos_q : 0 < (r + k * b^n : ℚ) := by exact_mod_cast hd_pos
    rw [div_pos_iff]
    left
    constructor
    · -- s^{n-1}*r + k*b*a^{n-1} > 0
      have ha_pow_pos : 0 < (a n k b r s : ℚ)^(n-1) := by
        cases n with
        | zero => simp
        | succ m =>
          apply pow_pos
          exact_mod_cast ha_pos
      have hs_pow_nonneg : 0 ≤ (s : ℚ)^(n-1) := by
        cases n with
        | zero => simp
        | succ m => apply pow_nonneg; exact_mod_cast hs
      have hr_q : (0 : ℚ) ≤ r := by exact_mod_cast hr
      have hk_q : (0 : ℚ) < k := by exact_mod_cast hk
      have hb_q : (0 : ℚ) < b := by exact_mod_cast hb
      have term1_nonneg : 0 ≤ (s : ℚ)^(n-1) * r := mul_nonneg hs_pow_nonneg hr_q
      have term2_pos : 0 < (k : ℚ) * b * (a n k b r s)^(n-1) := by
        apply mul_pos (mul_pos hk_q hb_q) ha_pow_pos
      linarith
    · exact hd_pos_q
  have hb_pos : (0 : ℚ) < b := by exact_mod_cast hb
  -- From pb = qa - rs^{n-1}, dividing by bq gives p/q = a/b - rs^{n-1}/(bq)
  have h_eq : p n k b r s / q n k b r s = a n k b r s / b - r * s^(n-1) / (b * q n k b r s) := by
    have hq_ne : q n k b r s ≠ 0 := ne_of_gt hq_pos
    have hb_ne : (b : ℚ) ≠ 0 := ne_of_gt hb_pos
    have hbq_ne : (b : ℚ) * q n k b r s ≠ 0 := mul_ne_zero hb_ne hq_ne
    -- From h_pb: p * b = q * a - r * s^{n-1}
    -- So p = (q * a - r * s^{n-1}) / b
    have hp_alt : p n k b r s = (q n k b r s * a n k b r s - r * s^(n-1)) / b := by
      rw [eq_div_iff hb_ne]; exact h_pb
    rw [hp_alt]
    -- LHS: (q * a - r * s^{n-1}) / b / q = (q * a - r * s^{n-1}) / (b * q)
    rw [div_div]
    -- Split the fraction
    rw [sub_div]
    -- First term: q * a / (b * q) = a / b (cancel q)
    have h1 : q n k b r s * ↑(a n k b r s) / (↑b * q n k b r s) = ↑(a n k b r s) / ↑b := by
      rw [mul_comm (q n k b r s) _, mul_div_mul_right _ _ hq_ne]
    rw [h1]
  rw [h_eq]
  -- Now show a/b - rs^{n-1}/(bq) ≤ a/b, i.e., rs^{n-1}/(bq) ≥ 0
  have hr_q : (0 : ℚ) ≤ r := by exact_mod_cast hr
  have hs_pow_nonneg : (0 : ℚ) ≤ s^(n-1) := by
    cases n with
    | zero => simp
    | succ m => apply pow_nonneg; exact_mod_cast hs
  have h_nonneg : 0 ≤ (r : ℚ) * s^(n-1) / (b * q n k b r s) := by
    apply div_nonneg
    · exact mul_nonneg hr_q hs_pow_nonneg
    · exact le_of_lt (mul_pos hb_pos hq_pos)
  linarith
end GroupTheoreticShannonCapacity.Construction
