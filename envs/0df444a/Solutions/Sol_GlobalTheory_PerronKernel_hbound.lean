-- Prove2me | solution 1 for GlobalTheory.PerronKernel.hbound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:35.554766+00:00
-- url     : https://prove2.me/submissions/d5ac475d-4273-4d7a-bfa8-bb3cb06e62e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Theorems.Thm_GlobalTheory_PerronKernel_norm_exp

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
theorem _root_.solution {L : ℝ} (hL : L ≠ 0) {t a b : ℝ} (h : t ≠ 0) (hab : a ≤ b) :
    ‖∫ x in a..b, cexp (L * ((x : ℂ) + t * I)) / ((x : ℂ) + t * I)‖
      ≤ (Real.exp (L * b) - Real.exp (L * a)) / (L * |t|) := by
  have hb : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.Ioc a b →
      ‖cexp (L * ((x : ℂ) + t * I)) / ((x : ℂ) + t * I)‖ ≤ Real.exp (L * x) / |t| := by
    refine Filter.Eventually.of_forall fun x _ => ?_
    rw [norm_div, norm_exp]
    apply div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.mpr h)
    simpa using Complex.abs_im_le_norm ((x : ℂ) + t * I)
  have hF : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => Real.exp (L * x) / (L * |t|))
      (Real.exp (L * x) / |t|) x := by
    intro x _
    refine (((hasDerivAt_id' x).const_mul L).exp.div_const (L * |t|)).congr_deriv ?_
    have ht : |t| ≠ 0 := abs_ne_zero.mpr h
    field_simp
  calc _ ≤ ∫ x in a..b, Real.exp (L * x) / |t| :=
        intervalIntegral.norm_integral_le_of_norm_le hab hb
          ((by fun_prop : Continuous fun x : ℝ => Real.exp (L * x) / |t|).intervalIntegrable _ _)
    _ = _ := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
          ((by fun_prop : Continuous fun x : ℝ => Real.exp (L * x) / |t|).intervalIntegrable _ _)]
        ring
end GlobalTheory.PerronKernel
