-- Prove2me | solution 1 for GlobalTheory.PerronKernel.near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:35.66278+00:00
-- url     : https://prove2.me/submissions/57a3c756-226d-4790-abb8-c1f1f9497884

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Theorems.Thm_GlobalTheory_PerronKernel_ne_zero_of_re
import Theorems.Thm_GlobalTheory_PerronKernel_cont_vinv
import Theorems.Thm_GlobalTheory_PerronKernel_vinv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronKernel
namespace GlobalTheory.PerronKernel
theorem _root_.solution (L : ℝ) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)‖
      ≤ Real.exp (L * c) * (Real.pi + 2 * (T * |L|)) := by
  have hc0 : c ≠ 0 := hc.ne'
  set g : ℝ → ℂ := fun t => (cexp (I * ((L * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I) with hg
  have hpt : ∀ t : ℝ, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)
      = (Real.exp (L * c) : ℂ) * (g t + ((c : ℂ) + t * I)⁻¹) := by
    intro t
    have hz : (c : ℂ) + t * I ≠ 0 := ne_zero_of_re hc0
    have he : cexp (L * ((c : ℂ) + t * I)) =
        (Real.exp (L * c) : ℂ) * cexp (I * ((L * t : ℝ) : ℂ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [hg]
    rw [he]
    field_simp
    ring
  have hgc : Continuous g := by
    simp only [hg]
    exact (by fun_prop : Continuous fun t : ℝ => cexp (I * ((L * t : ℝ) : ℂ)) - 1).div
      (by fun_prop) fun t => ne_zero_of_re hc0
  have hgb : ∀ t ∈ Set.uIoc (-T) T, ‖g t‖ ≤ |L| := by
    intro t _
    have hz : (c : ℂ) + t * I ≠ 0 := ne_zero_of_re hc0
    have hzn : 0 < ‖(c : ℂ) + t * I‖ := norm_pos_iff.mpr hz
    simp only [hg]
    rw [norm_div, div_le_iff₀ hzn]
    calc ‖cexp (I * ((L * t : ℝ) : ℂ)) - 1‖ ≤ ‖L * t‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = |L| * |t| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |L| * ‖(c : ℂ) + t * I‖ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg L)
        simpa using Complex.abs_im_le_norm ((c : ℂ) + t * I)
  have hint : (∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I))
      = (Real.exp (L * c) : ℂ) *
        ((∫ t in (-T)..T, g t) + ∫ t in (-T)..T, ((c : ℂ) + t * I)⁻¹) := by
    rw [intervalIntegral.integral_congr (fun t _ => hpt t), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hgc.intervalIntegrable _ _)
        ((cont_vinv hc0).intervalIntegrable _ _)]
  rw [hint, vinv hc0 T, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hg2 := intervalIntegral.norm_integral_le_of_norm_le_const hgb
  rw [show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]] at hg2
  have hat : |2 * Real.arctan (T / c)| ≤ Real.pi := by
    rw [abs_of_pos (by have := Real.arctan_pos.mpr (div_pos hT hc); linarith)]
    linarith [Real.arctan_lt_pi_div_two (T / c)]
  calc ‖(∫ t in (-T)..T, g t) + ((2 * Real.arctan (T / c) : ℝ) : ℂ)‖
      ≤ ‖∫ t in (-T)..T, g t‖ + ‖((2 * Real.arctan (T / c) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ |L| * (2 * T) + Real.pi := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith
    _ = Real.pi + 2 * (T * |L|) := by ring
end GlobalTheory.PerronKernel
