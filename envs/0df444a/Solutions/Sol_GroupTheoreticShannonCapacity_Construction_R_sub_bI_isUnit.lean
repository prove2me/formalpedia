-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.R_sub_bI_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:33:27.703247+00:00
-- url     : https://prove2.me/submissions/996429cd-87cd-4e2f-a574-9983b10294d9

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
theorem _root_.solution (n k b r : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hd : (r : ℤ) + (k : ℤ) * (b : ℤ) ^ n ≠ 0) :
    IsUnit (MAlpha.Rα n ((r : ℝ) / (k : ℝ)) - (b : ℝ) • 1) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
  have hdet := MAlpha.det_xRα_add_yI n hn 1 (-(b : ℝ)) ((r : ℝ) / (k : ℝ))
  simp only [one_smul, neg_smul] at hdet
  rw [sub_eq_add_neg, hdet, isUnit_iff_ne_zero]
  have h : (-1 : ℝ)^n * ((r : ℝ) / (k : ℝ)) + (-b : ℝ)^n =
      (-1 : ℝ)^n * ((r : ℝ) + (k : ℝ) * (b : ℝ)^n) / (k : ℝ) := by
    rw [neg_pow]; field_simp [hk_ne]; ring
  rw [h]
  have h_pow_ne := neg_one_pow_ne_zero n
  have hd_real : (r : ℝ) + (k : ℝ) * (b : ℝ)^n ≠ 0 := by exact_mod_cast hd
  have hprod_ne : (-1 : ℝ)^n * ((r : ℝ) + (k : ℝ) * (b : ℝ)^n) ≠ 0 :=
    mul_ne_zero h_pow_ne hd_real
  exact div_ne_zero hprod_ne hk_ne
end GroupTheoreticShannonCapacity.Construction
