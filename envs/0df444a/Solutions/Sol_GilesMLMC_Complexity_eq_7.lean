-- Prove2me | solution 1 for GilesMLMC.Complexity.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:39:33.205834+00:00
-- url     : https://prove2.me/submissions/d20e9b3c-73eb-46fa-9b68-ce867b4faa44

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

set_option autoImplicit false
open GilesMLMC.Complexity

theorem solution
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ ε : ℝ) (hα : 1 / 2 ≤ α) (hc₁ : 0 < c₁) (hε : 0 < ε) (hε1 : ε < Real.exp (-1))
    (L : ℕ) (hL : (L : ℤ) = Lchoice M T α c₁ ε) :
    ∑ l ∈ Finset.range (L + 1), (h M T l)⁻¹ <
      (M : ℝ) ^ 2 / ((M : ℝ) - 1) * (Real.sqrt 2 * c₁) ^ (1 / α) * ε ^ (-2 : ℝ) := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hαpos : 0 < α := by linarith
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos hM1
  have hε1' : ε < 1 := by
    have : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
    rw [Real.exp_zero] at this
    linarith
  set B : ℝ := (Real.sqrt 2 * c₁) ^ (1 / α) with hB
  have hBpos : 0 < B := by
    rw [hB]
    apply Real.rpow_pos_of_pos
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hc₁
  set A : ℝ := Real.sqrt 2 * c₁ * T ^ α * ε⁻¹ with hA
  have hApos : 0 < A := by
    rw [hA]
    have := Real.rpow_pos_of_pos hT α
    positivity
  set x : ℝ := Real.log A / (α * Real.log (M : ℝ)) with hx
  have hLx : (L : ℝ) < x + 1 := by
    have h1 : ((L : ℤ) : ℝ) = (Lchoice M T α c₁ ε : ℝ) := by rw [hL]
    have h2 : (Lchoice M T α c₁ ε : ℝ) < x + 1 := by
      have := Int.ceil_lt_add_one x
      simpa [Lchoice, hx, hA] using this
    simpa using h1.trans_lt h2
  -- M^x = A^(1/α)
  have hMx : (M : ℝ) ^ x = A ^ (1 / α) := by
    rw [Real.rpow_def_of_pos hMpos, Real.rpow_def_of_pos hApos]
    congr 1
    rw [hx]
    field_simp
  have hAexp : A ^ (1 / α) = B * T * (ε ^ (1 / α))⁻¹ := by
    rw [hA, hB]
    rw [Real.mul_rpow (by positivity) (inv_nonneg.mpr hε.le),
      Real.mul_rpow (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hc₁).le
        (Real.rpow_nonneg hT.le _),
      ← Real.rpow_mul hT.le, Real.inv_rpow hε.le]
    rw [mul_one_div_cancel hαpos.ne', Real.rpow_one]
  have hεpow : (ε ^ (1 / α))⁻¹ ≤ ε ^ (-2 : ℝ) := by
    have h1 : ε ^ (2 : ℝ) ≤ ε ^ (1 / α) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1'.le (by
        rw [div_le_iff₀ hαpos]; linarith)
    have h2 : ε ^ (-2 : ℝ) = (ε ^ (2 : ℝ))⁻¹ := Real.rpow_neg hε.le 2
    rw [h2]
    exact inv_anti₀ (Real.rpow_pos_of_pos hε _) h1
  have key : (M : ℝ) ^ (L + 1) < (M : ℝ) ^ 2 * (B * T * ε ^ (-2 : ℝ)) := by
    have h1 : (M : ℝ) ^ ((L : ℝ) + 1) < (M : ℝ) ^ (x + 2) :=
      Real.rpow_lt_rpow_of_exponent_lt hM1 (by linarith)
    have h2 : (M : ℝ) ^ ((L : ℝ) + 1) = (M : ℝ) ^ (L + 1) := by
      rw [← Real.rpow_natCast]; norm_num
    have h3 : (M : ℝ) ^ (x + 2) = (M : ℝ) ^ x * (M : ℝ) ^ 2 := by
      rw [Real.rpow_add hMpos]; norm_num
    rw [h2, h3, hMx, hAexp] at h1
    have h4 : B * T * (ε ^ (1 / α))⁻¹ ≤ B * T * ε ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left hεpow (by positivity)
    have h5 : (M : ℝ) ^ 2 * (B * T * (ε ^ (1 / α))⁻¹) ≤ (M : ℝ) ^ 2 * (B * T * ε ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith
  have hsum : ∑ l ∈ Finset.range (L + 1), (h M T l)⁻¹ =
      (∑ l ∈ Finset.range (L + 1), (M : ℝ) ^ l) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    simp [h, inv_div]
  have hgeom := geom_sum_mul (M : ℝ) (L + 1)
  have hMsub : 0 < (M : ℝ) - 1 := by linarith
  rw [hsum, div_lt_iff₀ hT]
  have h6 : (∑ l ∈ Finset.range (L + 1), (M : ℝ) ^ l) * ((M : ℝ) - 1) <
      (M : ℝ) ^ 2 * (B * T * ε ^ (-2 : ℝ)) := by
    rw [hgeom]; linarith
  have h7 : ∑ l ∈ Finset.range (L + 1), (M : ℝ) ^ l <
      (M : ℝ) ^ 2 * (B * T * ε ^ (-2 : ℝ)) / ((M : ℝ) - 1) := by
    rw [lt_div_iff₀ hMsub]; exact h6
  have h8 : (M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * ε ^ (-2 : ℝ) * T =
      (M : ℝ) ^ 2 * (B * T * ε ^ (-2 : ℝ)) / ((M : ℝ) - 1) := by
    field_simp
  rw [h8]; exact h7
