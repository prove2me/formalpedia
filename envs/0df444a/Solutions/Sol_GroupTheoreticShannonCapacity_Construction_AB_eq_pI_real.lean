-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.AB_eq_pI_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:52:57.801371+00:00
-- url     : https://prove2.me/submissions/2bd7c021-1939-406c-bf78-0b030051c09c

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_431fdefa9c23
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_5fe1a7aea33d
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
theorem _root_.solution (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hs : 1 ≤ s) (hb : 1 ≤ b)
    (hr : 0 ≤ r) (hd : r + k * b ^ n ≠ 0) (hn_num : s ^ n * r + k * (a n k b r s) ^ n ≠ 0) :
    (matrixA n k b r s).map (↑· : ℚ → ℝ) * (matrixB n k b r s).map (↑· : ℚ → ℝ) =
    (p n k b r s : ℝ) • 1 := by
  -- Using R_α factorizations:
  -- A = (p·R - pb·I) · (s·R - aI)⁻¹
  -- B = (s·R - aI) · (R - bI)⁻¹
  -- AB = (p·R - pb·I) · (R - bI)⁻¹ = p(R - bI)(R - bI)⁻¹ = pI
  have hs_ne : s ≠ 0 := by omega
  have hb_ne : b ≠ 0 := by omega
  have hr' : 0 ≤ r := hr
  have hs' : 0 ≤ s := by omega
  rw [A_Rα_form n k b r s hn hk hb hs hr hn_num,
    B_Rα_form n k b r s hn hd hk hb hr' hs']
  -- Now multiply and simplify
  -- Define α as in A_Rα_form and B_Rα_form to match their output exactly
  let α : ℚ := (r : ℚ) / (k : ℚ)
  set R := MAlpha.Rα n (α : ℝ) with hR
  set p_val : ℝ := (p n k b r s : ℝ) with hp_val
  set a_val : ℝ := (a n k b r s : ℝ) with ha_val
  set s_val : ℝ := (s : ℝ) with hs_val
  set b_val : ℝ := (b : ℝ) with hb_val
  -- Middle term: s·R - a·I
  set M := s_val • R - a_val • 1 with hM
  -- R - b·I
  set N := R - b_val • 1 with hN
  -- Show M is a unit (det ≠ 0)
  have hk_int_ne : k ≠ 0 := by omega
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast hk_int_ne
  have hM_det_ne : M.det ≠ 0 := by
    have h := MAlpha.det_xRα_add_yI n hn s_val (-a_val) (α : ℝ)
    simp only [← hR] at h  -- only replace Rα with R, don't touch neg_smul
    have hM_eq : M = s_val • R + (-a_val) • 1 := by simp only [hM, sub_eq_add_neg, neg_smul]
    rw [hM_eq, h]
    -- det = (-s_val)^n * (r/k) + (-a_val)^n
    -- Goal: show this is nonzero
    -- Convert to use s and a, and normalize coercions
    simp only [hs_val, ha_val]
    -- Convert α to (r:ℝ)/(k:ℝ)
    have hα_eq : (α : ℝ) = (r : ℝ) / (k : ℝ) := by
      simp only [α, Rat.cast_div, Rat.cast_intCast]
    rw [hα_eq]
    -- Goal: show (-s)^n * (r/k) + (-a)^n ≠ 0
    have ha_expand : (a n k b r s : ℝ) = (k : ℝ) * (b : ℝ)^n + (s : ℝ) * (b : ℝ) + (r : ℝ) := by
      simp only [a]; push_cast; ring
    -- Use neg_pow to factor out (-1)^n
    have h_neg_s : (-(s : ℝ))^n = (-1 : ℝ)^n * (s : ℝ)^n := by ring
    have h_neg_a : (-(a n k b r s : ℝ))^n = (-1 : ℝ)^n * (a n k b r s : ℝ)^n := by ring
    rw [h_neg_s, h_neg_a, ha_expand]
    have h_simpl : (-1 : ℝ)^n * (s : ℝ)^n * ((r : ℝ) / (k : ℝ)) +
        (-1 : ℝ)^n * ((k : ℝ) * (b : ℝ)^n + (s : ℝ) * (b : ℝ) + (r : ℝ))^n =
        (-1 : ℝ)^n * ((s : ℝ)^n * (r : ℝ) + (k : ℝ) *
          ((k : ℝ) * (b : ℝ)^n + (s : ℝ) * (b : ℝ) + (r : ℝ))^n) / (k : ℝ) := by
      field_simp [hk_ne]
    rw [h_simpl]
    have h_pow_ne := neg_one_pow_ne_zero n
    -- Use hn_num: s^n * r + k * a^n ≠ 0
    have hn_num_real : (s : ℝ)^n * (r : ℝ) + (k : ℝ) *
        ((k : ℝ) * (b : ℝ)^n + (s : ℝ) * (b : ℝ) + (r : ℝ))^n ≠ 0 := by
      have hn_num' : (s : ℝ)^n * (r : ℝ) + (k : ℝ) * (a n k b r s : ℝ)^n ≠ 0 := by
        exact_mod_cast hn_num
      rwa [ha_expand] at hn_num'
    exact div_ne_zero (mul_ne_zero h_pow_ne hn_num_real) hk_ne
  have hM_unit : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hM_det_ne
  have hM_det_unit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM_det_ne
  -- Show N is a unit (det ≠ 0)
  have hN_det_ne : N.det ≠ 0 := by
    have h := MAlpha.det_xRα_add_yI n hn 1 (-b_val) (α : ℝ)
    simp only [one_smul, ← hR] at h  -- only replace Rα with R, don't touch neg_smul
    have hN_eq : N = R + (-b_val) • 1 := by simp only [hN, sub_eq_add_neg, neg_smul]
    rw [hN_eq, h]
    -- det = (-1)^n * (r/k) + (-b_val)^n
    simp only [hb_val]
    -- Convert α to (r:ℝ)/(k:ℝ)
    have hα_eq : (α : ℝ) = (r : ℝ) / (k : ℝ) := by
      simp only [α, Rat.cast_div, Rat.cast_intCast]
    rw [hα_eq]
    -- Convert (-b)^n to (-1)^n * b^n
    have h_neg_b : (-(b : ℝ))^n = (-1 : ℝ)^n * (b : ℝ)^n := by ring
    rw [h_neg_b]
    have h_simpl : (-1 : ℝ)^n * ((r : ℝ) / (k : ℝ)) + (-1 : ℝ)^n * ((b : ℝ))^n =
        (-1 : ℝ)^n * ((r : ℝ) + (k : ℝ) * (b : ℝ)^n) / (k : ℝ) := by
      field_simp [hk_ne]
    rw [h_simpl]
    have h_pow_ne := neg_one_pow_ne_zero n
    have hd_real : (r : ℝ) + (k : ℝ) * (b : ℝ)^n ≠ 0 := by exact_mod_cast hd
    exact div_ne_zero (mul_ne_zero h_pow_ne hd_real) hk_ne
  have hN_det_unit : IsUnit N.det := isUnit_iff_ne_zero.mpr hN_det_ne
  -- Now do the algebra: (p·R - pb·I)·M⁻¹·M·N⁻¹ = (p·R - pb·I)·N⁻¹ = p·I
  -- First: M⁻¹ · M = 1
  have hM_inv_M : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM_det_unit
  have hN_mul_inv : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N hN_det_unit
  -- The matrix algebra calculation: the inverse cancellation gives us p·I
  -- (p·R - pb·I)·(s·R - a·I)⁻¹·(s·R - a·I)·(R - b·I)⁻¹
  -- = (p·R - pb·I)·(R - b·I)⁻¹   [by M⁻¹ * M = 1]
  -- = p(R - b·I)·(R - b·I)⁻¹    [factoring out p]
  -- = p·I                        [by N * N⁻¹ = 1]

  -- First: factor out p from (p·R - pb·I) = p·(R - b·I)
  have hP_factor : p_val • R - (p_val * b_val) • (1 : Matrix (Fin n) (Fin n) ℝ) = p_val • N := by
    simp only [hN, smul_sub]
    congr 1
    rw [smul_smul]
  -- Goal: ((p·R - pb·I) * M⁻¹) * (M * N⁻¹) = p·I
  -- The goal uses explicit Rα n (...). Need to match with our R, M, N.
  -- Use convert with explicit calc block
  convert_to ((p_val • R - (p_val * b_val) • 1) * M⁻¹) * (M * N⁻¹) = p_val • 1
  -- First use associativity to rearrange
  calc ((p_val • R - (p_val * b_val) • 1) * M⁻¹) * (M * N⁻¹)
      = (p_val • R - (p_val * b_val) • 1) * (M⁻¹ * (M * N⁻¹)) := by rw [Matrix.mul_assoc]
    _ = (p_val • R - (p_val * b_val) • 1) * ((M⁻¹ * M) * N⁻¹) := by rw [Matrix.mul_assoc]
    _ = (p_val • R - (p_val * b_val) • 1) * (1 * N⁻¹) := by rw [hM_inv_M]
    _ = (p_val • R - (p_val * b_val) • 1) * N⁻¹ := by rw [Matrix.one_mul]
    _ = (p_val • N) * N⁻¹ := by rw [hP_factor]
    _ = p_val • (N * N⁻¹) := by rw [Matrix.smul_mul]
    _ = p_val • 1 := by rw [hN_mul_inv]
    _ = (p n k b r s : ℝ) • 1 := by rfl
end GroupTheoreticShannonCapacity.Construction
