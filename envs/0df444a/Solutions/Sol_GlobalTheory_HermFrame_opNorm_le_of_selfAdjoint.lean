-- Prove2me | solution 1 for GlobalTheory.HermFrame.opNorm_le_of_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:27:54.669598+00:00
-- url     : https://prove2.me/submissions/edde5431-8ca0-41d2-9fdc-caf5fe840b95

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_form_add_left
import Theorems.Thm_GlobalTheory_HermFrame_form_add_right
import Theorems.Thm_GlobalTheory_HermFrame_form_smul_left
import Theorems.Thm_GlobalTheory_HermFrame_form_smul_right
import Theorems.Thm_GlobalTheory_HermFrame_form_sub_left
import Theorems.Thm_GlobalTheory_HermFrame_form_sub_right
import Theorems.Thm_GlobalTheory_HermFrame_conj_form
import Theorems.Thm_GlobalTheory_HermFrame_gnorm_sq
import Theorems.Thm_GlobalTheory_HermFrame_gnorm_parallelogram
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_HermFrame_le_two_mul_of_forall_scale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero

set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {H : Matrix m m ℂ} {K : Matrix n n ℂ} {L : Matrix l l ℂ}
namespace GlobalTheory.HermFrame
theorem _root_.solution (hH : H.PosSemidef) {T : Matrix m m ℂ}
    (hT : ∀ v w, form H (T *ᵥ v) w = form H v (T *ᵥ w)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, ‖form H (T *ᵥ v) v‖ ≤ c * gnorm H v ^ 2) : opNorm H H T ≤ c := by
  have h1 : ∀ v w, (form H (T *ᵥ v) w).re ≤ c / 2 * (gnorm H v ^ 2 + gnorm H w ^ 2) := by
    intro v w
    have e : (form H (T *ᵥ w) v).re = (form H (T *ᵥ v) w).re := by
      rw [hT w v, ← conj_form hH.isHermitian, conj_re]
    have a1 := (re_le_norm _).trans (h (v + w))
    have a2 := (abs_le.1 ((abs_re_le_norm _).trans (h (v - w)))).1
    have a3 := gnorm_parallelogram hH v w
    simp only [mulVec_add, mulVec_sub, form_add_left, form_add_right, form_sub_left,
      form_sub_right, add_re, sub_re] at a1 a2
    have a4 : c * gnorm H (v + w) ^ 2 + c * gnorm H (v - w) ^ 2 =
      2 * c * (gnorm H v ^ 2 + gnorm H w ^ 2) := by rw [← mul_add, a3]; ring
    linarith
  refine opNorm_le_of_bound hc fun v => ?_
  have h2 : (form H (T *ᵥ v) (T *ᵥ v)).re ≤ 2 * (c / 2) * gnorm H v * gnorm H (T *ᵥ v) := by
    refine le_two_mul_of_forall_scale (by linarith) (gnorm_nonneg _ _) (gnorm_nonneg _ _)
      fun s hs => ?_
    have hq : 0 < √s := Real.sqrt_pos.2 hs
    have := h1 ((√s : ℂ) • v) (((√s)⁻¹ : ℝ) • T *ᵥ v)
    rw [← Complex.coe_smul, mulVec_smul, form_smul_left, form_smul_right, gnorm_smul hH,
      gnorm_smul hH, conj_ofReal, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hq.ne', ofReal_one,
      one_mul, norm_real, norm_real, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs, inv_pow, Real.sq_sqrt hs.le] at this
    rwa [div_eq_inv_mul _ s]
  rw [← gnorm_sq hH] at h2
  rcases (gnorm_nonneg H (T *ᵥ v)).eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hc (gnorm_nonneg _ _)
  · nlinarith
end GlobalTheory.HermFrame
