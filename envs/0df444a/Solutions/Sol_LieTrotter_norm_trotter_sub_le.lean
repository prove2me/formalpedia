-- Prove2me | solution 1 for LieTrotter.norm_trotter_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:58:42.746532+00:00
-- url     : https://prove2.me/submissions/f5d63d88-f04e-4c7c-8eb4-bf1c4f3da172

module
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.NoncommRing
public import Definitions.Def_LieTrotter_Basic
public import Theorems.Thm_LieTrotter_norm_exp_le_exp_norm
public import Theorems.Thm_LieTrotter_norm_exp_mul_exp_sub_exp_add_le
public import Theorems.Thm_LieTrotter_norm_pow_sub_pow_le_of_norm_le
public import Theorems.Thm_LieTrotter_exp_pow_eq_exp_nsmul

set_option autoImplicit false
@[expose] public section
public section
open NormedSpace
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution (A B : 𝔸) (n : ℕ) (hn : 1 ≤ n) :
    ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
      ≤ (n : ℝ)⁻¹ * ((‖A‖ + ‖B‖) ^ 2 * (3 + (‖A‖ + ‖B‖)) * Real.exp (2 * (‖A‖ + ‖B‖))) := by
  set s := ‖A‖ + ‖B‖ with hs
  have hs0 : 0 ≤ s := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hexpAB : exp (A + B) = exp ((n : ℝ)⁻¹ • (A + B)) ^ n := by
    rw [exp_pow_eq_exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hnpos), one_smul]
  have hnormA : ‖(n : ℝ)⁻¹ • A‖ = (n : ℝ)⁻¹ * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
  have hnormB : ‖(n : ℝ)⁻¹ • B‖ = (n : ℝ)⁻¹ * ‖B‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
  have hsn : ‖(n : ℝ)⁻¹ • A‖ + ‖(n : ℝ)⁻¹ • B‖ = (n : ℝ)⁻¹ * s := by
    rw [hnormA, hnormB, hs]; ring
  -- the uniform norm ceiling e^{s/n} on all three step factors
  set C := Real.exp ((n : ℝ)⁻¹ * s) with hC
  have hC1 : 1 ≤ C := Real.one_le_exp (mul_nonneg hninv hs0)
  have hfac : ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)‖ ≤ C := by
    calc ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)‖
        ≤ ‖exp ((n : ℝ)⁻¹ • A)‖ * ‖exp ((n : ℝ)⁻¹ • B)‖ := norm_mul_le _ _
      _ ≤ Real.exp ‖(n : ℝ)⁻¹ • A‖ * Real.exp ‖(n : ℝ)⁻¹ • B‖ :=
          mul_le_mul (norm_exp_le_exp_norm _) (norm_exp_le_exp_norm _)
            (norm_nonneg _) (Real.exp_pos _).le
      _ = C := by rw [← Real.exp_add, hsn]
  have hfacAB : ‖exp ((n : ℝ)⁻¹ • (A + B))‖ ≤ C := by
    calc ‖exp ((n : ℝ)⁻¹ • (A + B))‖
        ≤ Real.exp ‖(n : ℝ)⁻¹ • (A + B)‖ := norm_exp_le_exp_norm _
      _ ≤ C := by
          rw [hC]
          refine Real.exp_le_exp.mpr ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
          have : ‖A + B‖ ≤ s := norm_add_le _ _
          exact mul_le_mul_of_nonneg_left this hninv
  have hCn : C ^ n ≤ Real.exp s := by
    rw [hC, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    rw [show (n : ℝ) * ((n : ℝ)⁻¹ * s) = ((n : ℝ) * (n : ℝ)⁻¹) * s from by
      ring, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul]
  have hstep := norm_exp_mul_exp_sub_exp_add_le
    ((n : ℝ)⁻¹ • A) ((n : ℝ)⁻¹ • B)
  rw [hsn, ← smul_add] at hstep
  have htel := norm_pow_sub_pow_le_of_norm_le hC1 hfac hfacAB n
  have hsle : (n : ℝ)⁻¹ * s ≤ s := by
    calc (n : ℝ)⁻¹ * s ≤ 1 * s := by
          gcongr
          rw [inv_le_one_iff₀]
          right; exact_mod_cast hn
      _ = s := one_mul s
  have hstep' : ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)
        - exp ((n : ℝ)⁻¹ • (A + B))‖
      ≤ ((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp s := by
    refine le_trans hstep ?_
    have h3le : 3 + (n : ℝ)⁻¹ * s ≤ 3 + s := by linarith
    have hele : Real.exp ((n : ℝ)⁻¹ * s) ≤ Real.exp s :=
      Real.exp_le_exp.mpr hsle
    have hsq : (0 : ℝ) ≤ ((n : ℝ)⁻¹ * s) ^ 2 := sq_nonneg _
    calc ((n : ℝ)⁻¹ * s) ^ 2 * (3 + (n : ℝ)⁻¹ * s)
          * Real.exp ((n : ℝ)⁻¹ * s)
        ≤ ((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp ((n : ℝ)⁻¹ * s) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h3le hsq) (Real.exp_pos _).le
      _ ≤ ((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp s := by
          refine mul_le_mul_of_nonneg_left hele ?_
          have : (0 : ℝ) ≤ 3 + s := by linarith
          positivity
  calc ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
      = ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n
          - exp ((n : ℝ)⁻¹ • (A + B)) ^ n‖ := by rw [hexpAB]
    _ ≤ n * C ^ n * ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)
          - exp ((n : ℝ)⁻¹ • (A + B))‖ := htel
    _ ≤ n * Real.exp s * (((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp s) := by
        have hcoef : (n : ℝ) * C ^ n ≤ n * Real.exp s :=
          mul_le_mul_of_nonneg_left hCn hnpos.le
        refine mul_le_mul hcoef hstep' (norm_nonneg _) ?_
        positivity
    _ = ((n : ℝ) * (n : ℝ)⁻¹)
          * ((n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * (Real.exp s * Real.exp s))) := by
        ring
    _ = (n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * Real.exp (2 * s)) := by
        rw [mul_inv_cancel₀ (ne_of_gt hnpos), one_mul, ← Real.exp_add,
          ← two_mul]
end LieTrotter
