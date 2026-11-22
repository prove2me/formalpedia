-- Prove2me | solution 1 for Lean4LPD.sector_bound_le_cZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:21.412974+00:00
-- url     : https://prove2.me/submissions/8c7d30e5-8495-4db3-974b-541b5fffd242

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_cZero_pow_nat
public import Theorems.Thm_Lean4LPD_chainWeight_zero
attribute [local simp] Lean4LPD.chainWeight_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {r G B a A P M : ℝ}
    (hr : 0 < r) (hG : 0 < G) (hB : 0 ≤ B) (ha0 : 0 ≤ a) (hA : 0 ≤ A)
    (ha : a ≤ A / r) (hP : 0 ≤ P) (hM : 0 ≤ M) (m : ℕ) :
    M * ((1 + B) * (a ^ (m + 1) * P) * ((r + 1) * G) ^ (m + 1) /
      (Nat.factorial (m + 1) : ℝ) *
      Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / ((r + 1) * G))) ≤
      (cZero r (m : ℝ) G B * G * A) ^ (m + 1) * P /
        (Nat.factorial (m + 1) : ℝ) * M := by
  have hX : 0 < (r + 1) * G := by positivity
  have hbase : a * ((r + 1) * G) ≤ ((r + 1) / r) * G * A := by
    calc
      a * ((r + 1) * G) ≤ (A / r) * ((r + 1) * G) :=
        mul_le_mul_of_nonneg_right ha hX.le
      _ = ((r + 1) / r) * G * A := by ring
  have hp := pow_le_pow_left₀ (mul_nonneg ha0 hX.le) hbase (m + 1)
  have hfrac : 9 / 4 * ((m : ℝ) + 1) ^ 2 / ((r + 1) * G) ≤
      9 / 4 * ((m : ℝ) + 1) ^ 2 / (r * G) := by
    apply (div_le_div_iff₀ hX (mul_pos hr hG)).mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have he := Real.exp_le_exp.mpr hfrac
  have hpair := mul_le_mul hp he (Real.exp_pos _).le (by positivity)
  have hcoef : 0 ≤ (1 + B) * P / (Nat.factorial (m + 1) : ℝ) * M := by positivity
  have hmul := mul_le_mul_of_nonneg_right hpair hcoef
  calc
    M * ((1 + B) * (a ^ (m + 1) * P) * ((r + 1) * G) ^ (m + 1) /
        (Nat.factorial (m + 1) : ℝ) *
        Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / ((r + 1) * G))) =
        (a * ((r + 1) * G)) ^ (m + 1) *
          Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / ((r + 1) * G)) *
          ((1 + B) * P / (Nat.factorial (m + 1) : ℝ) * M) := by
      simp only [mul_pow]
      ring
    _ ≤ ((r + 1) / r * G * A) ^ (m + 1) *
        Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / (r * G)) *
        ((1 + B) * P / (Nat.factorial (m + 1) : ℝ) * M) := hmul
    _ = (cZero r (m : ℝ) G B * G * A) ^ (m + 1) * P /
        (Nat.factorial (m + 1) : ℝ) * M := by
      simp only [mul_pow]
      rw [cZero_pow_nat hB]
      ring
end Lean4LPD
