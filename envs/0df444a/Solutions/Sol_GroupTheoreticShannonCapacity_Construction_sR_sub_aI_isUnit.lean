-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.sR_sub_aI_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:14.1281+00:00
-- url     : https://prove2.me/submissions/9a4a3f83-802b-4238-8eea-79ad60d39cdc

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_det_xR__add_yI_9d0b1d30422b

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
theorem _root_.solution (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hn_num : (s : ℤ) ^ n * (r : ℤ) +
      (k : ℤ) * (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)) ^ n ≠ 0) :
    IsUnit ((s : ℝ) • MAlpha.Rα n ((r : ℝ) / (k : ℝ)) -
      (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) : ℝ) • 1) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
  have hs_ne : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hs
  have hdet :=
    MAlpha.det_xRα_add_yI n hn (s : ℝ) (-(a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)) ((r : ℝ) / (k : ℝ))
  simp only [neg_smul] at hdet
  rw [sub_eq_add_neg, hdet, isUnit_iff_ne_zero]
  -- det = (-s)^n * (r/k) + (-a)^n
  have h_neg_s : (-(s : ℝ))^n = (-1 : ℝ)^n * (s : ℝ)^n := by ring
  have h_neg_a : (-(a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ))^n =
      (-1 : ℝ)^n * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)^n := by ring
  rw [h_neg_s, h_neg_a]
  have h_simpl :
      (-1 : ℝ)^n * (s : ℝ)^n * ((r : ℝ) / (k : ℝ)) +
        (-1 : ℝ)^n * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)^n =
      (-1 : ℝ)^n * ((s : ℝ)^n * (r : ℝ) +
        (k : ℝ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)^n) / (k : ℝ) := by
    field_simp [hk_ne]
  rw [h_simpl]
  have h_pow_ne := neg_one_pow_ne_zero n
  have hn_num_real : (s : ℝ)^n * (r : ℝ) + (k : ℝ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)^n ≠ 0 := by
    exact_mod_cast hn_num
  exact div_ne_zero (mul_ne_zero h_pow_ne hn_num_real) hk_ne
end GroupTheoreticShannonCapacity.Construction
