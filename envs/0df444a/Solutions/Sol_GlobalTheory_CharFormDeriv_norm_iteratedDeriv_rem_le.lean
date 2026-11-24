-- Prove2me | solution 1 for GlobalTheory.CharFormDeriv.norm_iteratedDeriv_rem_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:36.231044+00:00
-- url     : https://prove2.me/submissions/b9b1c0eb-4072-46c8-af44-46b94e5f6d1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Theorems.Thm_GlobalTheory_CharFormDeriv_iteratedDeriv_const_mul_cexp
import Theorems.Thm_GlobalTheory_CharFormDeriv_deriv_affine_cexp
import Theorems.Thm_GlobalTheory_CharFormDeriv_norm_cexp_mul_I_sub_one_le
import Theorems.Thm_GlobalTheory_CharFormDeriv_norm_cexp_mul_I_sub_one_sub_le
import Theorems.Thm_GlobalTheory_CharFormDeriv_rem_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv
namespace GlobalTheory.CharFormDeriv
theorem _root_.solution {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) (i : ℕ) (y : ℝ) :
    ‖iteratedDeriv i (rem t) y‖ ≤ 3 * |t| * (1 + |y|) ^ 2 := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  have habs : 0 < |t| := abs_pos.mpr ht0
  have hy : 0 ≤ |y| := abs_nonneg y
  have hexp : (I * t) * (y : ℂ) = ((t * y : ℝ) : ℂ) * I := by push_cast; ring
  have hnexp : ‖Complex.exp ((I * t) * (y : ℂ))‖ = 1 := by
    rw [hexp, Complex.norm_exp_ofReal_mul_I]
  have hy1 : y ^ 2 ≤ (1 + |y|) ^ 2 := by
    rw [← sq_abs y]; nlinarith
  have hy2 : |y| ≤ (1 + |y|) ^ 2 := by nlinarith
  have hrem : rem t = fun y : ℝ => (t : ℂ)⁻¹ * Complex.exp ((I * t) * y) + (-I) * y + (-(t : ℂ)⁻¹) := rfl
  have hd1 : deriv (rem t) = fun y : ℝ => (t : ℂ)⁻¹ * (I * t) * Complex.exp ((I * t) * y) + (-I) := by
    rw [hrem, deriv_affine_cexp]
  match i with
  | 0 =>
    rw [iteratedDeriv_zero, rem_eq ht0, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    have h3 := norm_cexp_mul_I_sub_one_sub_le (t * y)
    calc |t|⁻¹ * ‖Complex.exp (((t * y : ℝ) : ℂ) * I) - 1 - ((t * y : ℝ) : ℂ) * I‖
        ≤ |t|⁻¹ * (3 * (t * y) ^ 2) := by gcongr
      _ = 3 * |t| * y ^ 2 := by
        rw [mul_pow, ← sq_abs t]; field_simp
      _ ≤ 3 * |t| * (1 + |y|) ^ 2 := by gcongr
  | 1 =>
    rw [iteratedDeriv_one, hd1]
    simp only
    have e : (t : ℂ)⁻¹ * (I * t) * Complex.exp ((I * t) * y) + (-I)
        = I * (Complex.exp (((t * y : ℝ) : ℂ) * I) - 1) := by
      rw [hexp]; field_simp; ring
    rw [e, norm_mul, Complex.norm_I, one_mul]
    calc ‖Complex.exp (((t * y : ℝ) : ℂ) * I) - 1‖ ≤ 2 * |t * y| := norm_cexp_mul_I_sub_one_le _
      _ = 2 * |t| * |y| := by rw [abs_mul]; ring
      _ ≤ 3 * |t| * (1 + |y|) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hy2 habs.le
        nlinarith
  | m + 2 =>
    have hd1' : deriv (rem t) = fun y : ℝ =>
        ((t : ℂ)⁻¹ * (I * t)) * Complex.exp ((I * t) * y) + 0 * y + (-I) := by
      rw [hd1]; funext y; ring
    have hd2 : deriv (deriv (rem t)) = fun y : ℝ =>
        ((t : ℂ)⁻¹ * (I * t) * (I * t)) * Complex.exp ((I * t) * y) := by
      rw [hd1', deriv_affine_cexp]; funext y; ring
    rw [iteratedDeriv_succ', iteratedDeriv_succ', hd2, iteratedDeriv_const_mul_cexp]
    simp only
    rw [norm_mul, hnexp, mul_one]
    simp only [norm_mul, norm_pow, norm_inv, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    have hp : |t| ^ m ≤ 1 := pow_le_one₀ habs.le ht1
    calc |t|⁻¹ * |t| * |t| * |t| ^ m = |t| * |t| ^ m := by field_simp
      _ ≤ |t| * 1 := by gcongr
      _ ≤ 3 * |t| * (1 + |y|) ^ 2 := by
        have : 1 ≤ (1 + |y|) ^ 2 := by nlinarith
        nlinarith
end GlobalTheory.CharFormDeriv
