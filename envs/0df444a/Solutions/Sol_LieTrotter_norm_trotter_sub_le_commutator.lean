-- Prove2me | solution 1 for LieTrotter.norm_trotter_sub_le_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:12:51.81429+00:00
-- url     : https://prove2.me/submissions/703ff70d-f5ae-4b78-a8ea-6e55642d358d

module
public import Definitions.Def_LieTrotter_Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Definitions.Def_LieTrotter_Commutator
public import Theorems.Thm_LieTrotter_norm_exp_smul_le
public import Theorems.Thm_LieTrotter_norm_exp_mul_exp_sub_exp_add_le_commutator
public import Theorems.Thm_LieTrotter_norm_pow_succ_sub_pow_succ_le
public import Theorems.Thm_LieTrotter_exp_pow_eq_exp_nsmul


set_option autoImplicit false
@[expose] public section
public section
open NormedSpace Set
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution (A B : 𝔸) (n : ℕ) (hn : 1 ≤ n) :
    ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
      ≤ ‖A * B - B * A‖ / (2 * n) * Real.exp (‖A‖ + ‖B‖) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  push_cast
  set N : ℝ := (m : ℝ) + 1 with hN
  have hNpos : 0 < N := by positivity
  have hNinv : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
  set s := ‖A‖ + ‖B‖ with hs
  set C := Real.exp (N⁻¹ * s) with hC
  have hnorm : ∀ X : 𝔸, ‖N⁻¹ • X‖ = N⁻¹ * ‖X‖ := fun X => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hNinv]
  -- the factors
  have hfac : ‖exp (N⁻¹ • A) * exp (N⁻¹ • B)‖ ≤ C := by
    calc ‖exp (N⁻¹ • A) * exp (N⁻¹ • B)‖ ≤ ‖exp (N⁻¹ • A)‖ * ‖exp (N⁻¹ • B)‖ := norm_mul_le _ _
      _ ≤ Real.exp (N⁻¹ * ‖A‖) * Real.exp (N⁻¹ * ‖B‖) :=
          mul_le_mul (norm_exp_smul_le A hNinv) (norm_exp_smul_le B hNinv) (norm_nonneg _)
            (Real.exp_pos _).le
      _ = C := by rw [hC, ← Real.exp_add, hs, mul_add]
  have hfacAB : ‖exp (N⁻¹ • (A + B))‖ ≤ C :=
    (norm_exp_smul_le (A + B) hNinv).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_add_le A B) hNinv))
  have hexpAB : exp (A + B) = exp (N⁻¹ • (A + B)) ^ (m + 1) := by
    rw [exp_pow_eq_exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [show ((m + 1 : ℕ) : ℝ) * N⁻¹ = 1 by push_cast; exact mul_inv_cancel₀ hNpos.ne', one_smul]
  -- the one step
  have hcomm : N⁻¹ • A * (N⁻¹ • B) - N⁻¹ • B * (N⁻¹ • A) = (N⁻¹ * N⁻¹) • (A * B - B * A) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
  have hstep : ‖exp (N⁻¹ • A) * exp (N⁻¹ • B) - exp (N⁻¹ • (A + B))‖
      ≤ N⁻¹ * N⁻¹ * ‖A * B - B * A‖ / 2 * C := by
    have h := norm_exp_mul_exp_sub_exp_add_le_commutator (N⁻¹ • A) (N⁻¹ • B)
    rw [hcomm, ← smul_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      hnorm, hnorm, ← mul_add] at h
    exact h
  have htel := norm_pow_succ_sub_pow_succ_le hfac hfacAB m
  have hCpow : C ^ m * C = Real.exp s := by
    rw [← pow_succ, hC, ← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [← mul_assoc, ← hN, mul_inv_cancel₀ hNpos.ne', one_mul]
  calc ‖(exp (N⁻¹ • A) * exp (N⁻¹ • B)) ^ (m + 1) - exp (A + B)‖
      = ‖(exp (N⁻¹ • A) * exp (N⁻¹ • B)) ^ (m + 1) - exp (N⁻¹ • (A + B)) ^ (m + 1)‖ := by
        rw [← hexpAB]
    _ ≤ (m + 1) * C ^ m * ‖exp (N⁻¹ • A) * exp (N⁻¹ • B) - exp (N⁻¹ • (A + B))‖ := htel
    _ ≤ (m + 1) * C ^ m * (N⁻¹ * N⁻¹ * ‖A * B - B * A‖ / 2 * C) := by gcongr
    _ = ‖A * B - B * A‖ / (2 * N) * (C ^ m * C) * (N * N⁻¹) := by rw [← hN]; ring_nf
    _ = ‖A * B - B * A‖ / (2 * N) * Real.exp s := by
        rw [hCpow, mul_inv_cancel₀ hNpos.ne', mul_one]
end LieTrotter
