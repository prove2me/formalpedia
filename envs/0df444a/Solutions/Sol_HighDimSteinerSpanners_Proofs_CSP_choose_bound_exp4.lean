-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.choose_bound_exp4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:37.663607+00:00
-- url     : https://prove2.me/submissions/e817e3d1-e84c-45a3-a144-522bd01b6cde

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Definitions
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution (U S m_sz r B : ℕ) (hB : 1 ≤ B) (hU : U ≤ B * r) (hS : S ≤ m_sz) :
    (U.choose S : ℝ) ≤ (B : ℝ) ^ m_sz * (4 : ℝ) ^ r := by
  have hexp4 : Real.exp (r : ℝ) ≤ (4 : ℝ) ^ r := by
    have h1 : Real.exp (r : ℝ) = (Real.exp 1) ^ r := by simp
    have he4 : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
    rw [h1]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he4 r
  have h1 : (U.choose S : ℝ) ≤ (U : ℝ) ^ S / (S.factorial : ℝ) := Nat.choose_le_pow_div S U
  have hU_r : (U : ℝ) ≤ (B : ℝ) * (r : ℝ) := by exact_mod_cast hU
  have h2 : (U : ℝ) ^ S / (S.factorial : ℝ) ≤
      ((B : ℝ) * (r : ℝ)) ^ S / (S.factorial : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg U) hU_r S) (Nat.cast_nonneg _)
  have h3 : ((B : ℝ) * (r : ℝ)) ^ S / (S.factorial : ℝ) =
      (B : ℝ) ^ S * ((r : ℝ) ^ S / (S.factorial : ℝ)) := by
    rw [mul_pow, mul_div_assoc]
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBs : (B : ℝ) ^ S ≤ (B : ℝ) ^ m_sz := pow_le_pow_right₀ hB1 hS
  have hrs : (r : ℝ) ^ S / (S.factorial : ℝ) ≤ (4 : ℝ) ^ r :=
    le_trans (Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) S) hexp4
  have h4 : (B : ℝ) ^ S * ((r : ℝ) ^ S / (S.factorial : ℝ)) ≤ (B : ℝ) ^ m_sz * (4 : ℝ) ^ r :=
    mul_le_mul hBs hrs (by positivity) (by positivity)
  linarith
end HighDimSteinerSpanners.Proofs.CSP
