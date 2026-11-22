-- Prove2me | solution 1 for HypercliqueFalse.choice_of_q
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T13:12:22.278601+00:00
-- url     : https://prove2.me/submissions/c2a0af32-41a9-4520-ac7c-7f0fd8aa0d2c

import Mathlib

set_option autoImplicit false

theorem solution (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (q : ℕ)
    (hq : q = 2 ^ ⌈(2 / δ) * Real.logb 2 (1 / δ)⌉₊) :
    (2 / (q : ℝ)) ^ δ = (2 : ℝ) ^ (-δ * (Real.logb 2 q - 1)) ∧
      (2 : ℝ) ^ (-δ * (Real.logb 2 q - 1)) ≤ (2 : ℝ) ^ δ * δ ^ 2 ∧
      (2 : ℝ) ^ δ * δ ^ 2 ≤ δ / 4 ∧
      Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ) ≤ δ / 2 ∧
      Real.logb 2 q ≤ 3 / δ * Real.logb 2 (1 / δ) ∧
      δ ^ 2 / (6 * Real.logb 2 (1 / δ)) ≤
        (δ - Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ)) / Real.logb 2 q := by
  have hδne : δ ≠ 0 := hδ.ne'
  -- L ≥ 3
  have hL3 : (3 : ℝ) ≤ Real.logb 2 (1 / δ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < 1 / δ)]
    rw [show (2 : ℝ) ^ (3 : ℝ) = 8 by norm_num, le_div_iff₀ hδ]
    nlinarith
  have hLpos : 0 < Real.logb 2 (1 / δ) := by linarith
  -- the ceiling k
  set k : ℕ := ⌈(2 / δ) * Real.logb 2 (1 / δ)⌉₊ with hkdef
  have hqk : q = 2 ^ k := by rw [hq, hkdef]
  have hk_lower : (2 / δ) * Real.logb 2 (1 / δ) ≤ (k : ℝ) := by
    rw [hkdef]
    exact Nat.le_ceil _
  have hk_upper : (k : ℝ) < (2 / δ) * Real.logb 2 (1 / δ) + 1 := by
    rw [hkdef]
    exact Nat.ceil_lt_add_one (mul_nonneg (by positivity) hLpos.le)
  have hk_ge_one : 1 ≤ k := by
    have h2d : (16 : ℝ) ≤ 2 / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith
    have hprod : (16 : ℝ) * 3 ≤ (2 / δ) * Real.logb 2 (1 / δ) :=
      mul_le_mul h2d hL3 (by norm_num) (by linarith)
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by linarith [hk_lower, hprod]
    exact_mod_cast h1
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk_ge_one)
  -- logb 2 q = k
  have hlogq : Real.logb 2 (q : ℝ) = (k : ℝ) := by
    rw [hqk, Nat.cast_pow]
    simp only [Nat.cast_ofNat]
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    ring
  -- (2/q)^δ = 2^{δ(1-k)}
  have h2q : (2 / (q : ℝ)) ^ δ = (2 : ℝ) ^ (δ * (1 - (k : ℝ))) := by
    rw [hqk, Nat.cast_pow]
    simp only [Nat.cast_ofNat]
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)]
    rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  -- δ² = 2^{-2L}
  have h2mL : (2 : ℝ) ^ (-Real.logb 2 (1 / δ)) = δ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
      (by positivity : 0 < 1 / δ)]
    rw [one_div, inv_inv]
  have hδsq : (2 : ℝ) ^ (-2 * Real.logb 2 (1 / δ)) = δ ^ 2 := by
    rw [show -2 * Real.logb 2 (1 / δ) = (-Real.logb 2 (1 / δ)) * 2 by ring]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h2mL]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- exponent comparison for clause 2
  have hexp_le : -(δ * (k : ℝ)) ≤ -2 * Real.logb 2 (1 / δ) := by
    have h : 2 * Real.logb 2 (1 / δ) ≤ δ * (k : ℝ) := by
      have h1 : δ * ((2 / δ) * Real.logb 2 (1 / δ)) ≤ δ * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hk_lower hδ.le
      have h2 : δ * ((2 / δ) * Real.logb 2 (1 / δ)) = 2 * Real.logb 2 (1 / δ) := by
        field_simp
      linarith
    linarith
  have hk2 : (2 : ℝ) ^ (-(δ * (k : ℝ))) ≤ δ ^ 2 := by
    rw [← hδsq]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_le
  -- clause 3
  have hcl3 : (2 : ℝ) ^ δ * δ ^ 2 ≤ δ / 4 := by
    have h2d : (2 : ℝ) ^ δ ≤ 2 := by
      calc (2 : ℝ) ^ δ ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith : δ ≤ 1)
        _ = 2 := by rw [Real.rpow_one]
    have hδ2 : δ * δ ≤ δ * (1 / 8) := mul_le_mul_of_nonneg_left hδ8 hδ.le
    have hd2 : (2 : ℝ) * δ ^ 2 ≤ δ / 4 := by nlinarith
    calc (2 : ℝ) ^ δ * δ ^ 2 ≤ 2 * δ ^ 2 := mul_le_mul_of_nonneg_right h2d (sq_nonneg δ)
      _ ≤ δ / 4 := hd2
  -- the clipping factor is ≤ δ/4
  have hz_le : (2 / (q : ℝ)) ^ δ ≤ δ / 4 := by
    rw [h2q]
    rw [show δ * (1 - (k : ℝ)) = δ + (-(δ * (k : ℝ))) by ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    calc (2 : ℝ) ^ δ * (2 : ℝ) ^ (-(δ * (k : ℝ))) ≤ (2 : ℝ) ^ δ * δ ^ 2 :=
          mul_le_mul_of_nonneg_left hk2 (by positivity)
      _ ≤ δ / 4 := hcl3
  -- clause 1
  have hcl1 : (2 / (q : ℝ)) ^ δ = (2 : ℝ) ^ (-δ * (Real.logb 2 q - 1)) := by
    rw [hlogq, h2q]
    congr 1
    ring
  -- clause 2
  have hcl2 : (2 : ℝ) ^ (-δ * (Real.logb 2 q - 1)) ≤ (2 : ℝ) ^ δ * δ ^ 2 := by
    rw [hlogq]
    rw [show -δ * ((k : ℝ) - 1) = δ + (-(δ * (k : ℝ))) by ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hk2 (by positivity)
  -- clause 4
  have hcl4 : Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ) ≤ δ / 2 := by
    have h1z : 0 < 1 + (2 / (q : ℝ)) ^ δ := by positivity
    have h1d : 0 < 1 + δ / 4 := by linarith
    have hmono : Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ) ≤ Real.logb 2 (1 + δ / 4) :=
      (Real.logb_le_logb (b := 2) (by norm_num : (1 : ℝ) < 2) h1z h1d).mpr (by linarith)
    have hmain : Real.logb 2 (1 + δ / 4) ≤ δ / 2 := by
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogineq : Real.log (1 + δ / 4) ≤ δ / 4 := by
        have := Real.log_le_sub_one_of_pos h1d
        linarith
      change Real.log (1 + δ / 4) / Real.log 2 ≤ δ / 2
      rw [div_le_iff₀ hlog2pos]
      nlinarith
    linarith
  -- clause 5
  have hk_le : (k : ℝ) ≤ 3 / δ * Real.logb 2 (1 / δ) := by
    have hLd : (1 : ℝ) ≤ Real.logb 2 (1 / δ) / δ := by
      rw [le_div_iff₀ hδ]
      linarith
    calc (k : ℝ) ≤ (2 / δ) * Real.logb 2 (1 / δ) + 1 := le_of_lt hk_upper
      _ ≤ (2 / δ) * Real.logb 2 (1 / δ) + Real.logb 2 (1 / δ) / δ := by linarith
      _ = 3 / δ * Real.logb 2 (1 / δ) := by ring
  have hcl5 : Real.logb 2 q ≤ 3 / δ * Real.logb 2 (1 / δ) := by
    rw [hlogq]
    exact hk_le
  -- clause 6
  have hcl6 : δ ^ 2 / (6 * Real.logb 2 (1 / δ)) ≤
      (δ - Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ)) / Real.logb 2 q := by
    rw [hlogq]
    have hnum : δ / 2 ≤ δ - Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ) := by linarith
    have h1 : (δ / 2) / ((3 / δ) * Real.logb 2 (1 / δ)) ≤ (δ / 2) / (k : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) hkR_pos hk_le
    have h2 : (δ / 2) / (k : ℝ) ≤
        (δ - Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ)) / (k : ℝ) :=
      div_le_div_of_nonneg_right hnum hkR_pos.le
    calc δ ^ 2 / (6 * Real.logb 2 (1 / δ)) =
          (δ / 2) / ((3 / δ) * Real.logb 2 (1 / δ)) := by
          field_simp
          ring
      _ ≤ (δ / 2) / (k : ℝ) := h1
      _ ≤ (δ - Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ)) / (k : ℝ) := h2
  exact ⟨hcl1, hcl2, hcl3, hcl4, hcl5, hcl6⟩

