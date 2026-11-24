-- Prove2me | solution 1 for GlobalTheory.PerronKernel.rect_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:39:56.806553+00:00
-- url     : https://prove2.me/submissions/8a7b2b0a-ce6e-44df-8d35-1ceb41ff0ead

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Theorems.Thm_GlobalTheory_PerronKernel_ne_zero_of_re
import Theorems.Thm_GlobalTheory_PerronKernel_ne_zero_of_im
import Theorems.Thm_GlobalTheory_PerronKernel_cont_vinv
import Theorems.Thm_GlobalTheory_PerronKernel_cont_hinv
import Theorems.Thm_GlobalTheory_PerronKernel_vinv
import Theorems.Thm_GlobalTheory_PerronKernel_hinv

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
theorem _root_.solution (L : ℝ) {a b T : ℝ} (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    (∫ x in a..b, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    - (∫ x in a..b, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
    + I * (∫ t in (-T)..T, cexp (L * ((b : ℂ) + t * I)) / ((b : ℂ) + t * I))
    - I * (∫ t in (-T)..T, cexp (L * ((a : ℂ) + t * I)) / ((a : ℂ) + t * I))
      = 2 * Real.pi * I := by
  set D : ℂ → ℂ := dslope (fun z : ℂ => cexp (L * z)) 0 with hD
  have hDd : Differentiable ℂ D := by
    have : DifferentiableOn ℂ D Set.univ :=
      (differentiableOn_dslope Filter.univ_mem).2 (by fun_prop)
    exact fun z => (this z trivial).differentiableAt Filter.univ_mem
  have hsplit : ∀ z : ℂ, z ≠ 0 → cexp (L * z) / z = D z + z⁻¹ := by
    intro z hz
    rw [hD, dslope_of_ne _ hz, slope_def_field]
    simp only [mul_zero, Complex.exp_zero, sub_zero]
    field_simp
    ring
  have hTn : -T ≠ 0 := by linarith
  have ha0 : a ≠ 0 := ha.ne
  have hb0 : b ≠ 0 := hb.ne'
  have hDc : Continuous D := hDd.continuous
  have sb : (∫ x in a..b, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      = (∫ x in a..b, D ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) + ∫ x in a..b, ((x : ℂ) + ((-T : ℝ) : ℂ) * I)⁻¹ := by
    have i1 : IntervalIntegrable (fun x : ℝ => D ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) MeasureTheory.volume a b :=
      (hDc.comp (by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + ((-T : ℝ) : ℂ) * I))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 ((cont_hinv hTn).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun x _ => hsplit _ (ne_zero_of_im hTn)
  have st : (∫ x in a..b, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
      = (∫ x in a..b, D ((x : ℂ) + T * I)) + ∫ x in a..b, ((x : ℂ) + T * I)⁻¹ := by
    have i1 : IntervalIntegrable (fun x : ℝ => D ((x : ℂ) + T * I)) MeasureTheory.volume a b :=
      (hDc.comp (by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + T * I))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 ((cont_hinv hT.ne').intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun x _ => hsplit _ (ne_zero_of_im hT.ne')
  have sr : (∫ t in (-T)..T, cexp (L * ((b : ℂ) + t * I)) / ((b : ℂ) + t * I))
      = (∫ t in (-T)..T, D ((b : ℂ) + t * I)) + ∫ t in (-T)..T, ((b : ℂ) + t * I)⁻¹ := by
    have i1 : IntervalIntegrable (fun t : ℝ => D ((b : ℂ) + t * I)) MeasureTheory.volume (-T) T :=
      (hDc.comp (by fun_prop : Continuous fun t : ℝ => ((b : ℂ) + t * I))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 ((cont_vinv hb0).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun t _ => hsplit _ (ne_zero_of_re hb0)
  have sl : (∫ t in (-T)..T, cexp (L * ((a : ℂ) + t * I)) / ((a : ℂ) + t * I))
      = (∫ t in (-T)..T, D ((a : ℂ) + t * I)) + ∫ t in (-T)..T, ((a : ℂ) + t * I)⁻¹ := by
    have i1 : IntervalIntegrable (fun t : ℝ => D ((a : ℂ) + t * I)) MeasureTheory.volume (-T) T :=
      (hDc.comp (by fun_prop : Continuous fun t : ℝ => ((a : ℂ) + t * I))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 ((cont_vinv ha0).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun t _ => hsplit _ (ne_zero_of_re ha0)
  have h1 : ((a : ℂ) + ((-T : ℝ) : ℂ) * I).re = a := by simp
  have h2 : ((a : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
  have h3 : ((b : ℂ) + (T : ℂ) * I).re = b := by simp
  have h4 : ((b : ℂ) + (T : ℂ) * I).im = T := by simp
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    D ((a : ℂ) + ((-T : ℝ) : ℂ) * I) ((b : ℂ) + T * I) hDd.differentiableOn
  rw [h1, h2, h3, h4] at hrect
  simp only [smul_eq_mul] at hrect
  have e1 := hinv hT.ne' a b
  have e2 := vinv hb0 T
  have e3 := vinv ha0 T
  have r2 : Real.arctan (T / b) = Real.pi / 2 - Real.arctan (b / T) := by
    rw [← inv_div, Real.arctan_inv_of_pos (div_pos hb hT)]
  have r3 : Real.arctan (T / a) = -(Real.pi / 2) - Real.arctan (a / T) := by
    rw [← inv_div, Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha hT)]
  rw [r2] at e2
  rw [r3] at e3
  rw [sb, st, sr, sl]
  linear_combination (norm := skip) hrect + e1 + I * e2 - I * e3
  push_cast
  ring
end GlobalTheory.PerronKernel
