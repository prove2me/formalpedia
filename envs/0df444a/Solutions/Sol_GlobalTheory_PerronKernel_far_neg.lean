-- Prove2me | solution 1 for GlobalTheory.PerronKernel.far_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:38:51.247224+00:00
-- url     : https://prove2.me/submissions/fb82f63b-c34e-49e2-8a92-a832100422a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Theorems.Thm_GlobalTheory_PerronKernel_vbound
import Theorems.Thm_GlobalTheory_PerronKernel_hbound
import Theorems.Thm_GlobalTheory_PerronKernel_rect_right
import Theorems.Thm_GlobalTheory_PerronKernel_le_of_forall_large
import Theorems.Thm_GlobalTheory_PerronKernel_norm_le_three

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
theorem _root_.solution {L c T : ℝ} (hL : L < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)‖
      ≤ 2 * Real.exp (L * c) / (T * |L|) := by
  apply le_of_forall_large (c := c) hc (K := 2 * T * Real.exp (L * c)) (by positivity)
  intro U hU
  have hU0 : 0 < U := lt_of_lt_of_le hc hU
  have hR := rect_right L T hc hU
  have h3 := norm_le_three
    (x := ∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I))
    (p := ∫ x in c..U, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    (q := ∫ x in c..U, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
    (r := ∫ t in (-T)..T, cexp (L * ((U : ℂ) + t * I)) / ((U : ℂ) + t * I)) (Or.inl (by linear_combination -hR))
  have hLT : 0 < T * -L := mul_pos hT (neg_pos.mpr hL)
  have key : ∀ s : ℝ, |s| = T → (Real.exp (L * U) - Real.exp (L * c)) / (L * |s|)
      ≤ Real.exp (L * c) / (T * |L|) := by
    intro s hs
    rw [hs, abs_of_neg hL, show L * T = -(T * -L) by ring, div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (L * U)]) hLT.le
  have hp := (hbound hL.ne (t := -T) (neg_ne_zero.mpr hT.ne') hU).trans
    (key (-T) (by rw [abs_neg, abs_of_pos hT]))
  have hq := (hbound hL.ne (t := T) hT.ne' hU).trans (key T (abs_of_pos hT))
  have hexp : Real.exp (L * U) ≤ Real.exp (L * c) := Real.exp_le_exp.mpr (by nlinarith)
  have hr : Real.exp (L * U) / |U| * (2 * T) ≤ 2 * T * Real.exp (L * c) / U := by
    rw [abs_of_pos hU0, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hU0.le
  have hr' := (vbound L (σ := U) hU0.ne' hT.le).trans hr
  have h2 : 2 * Real.exp (L * c) / (T * |L|) =
      Real.exp (L * c) / (T * |L|) + Real.exp (L * c) / (T * |L|) := by ring
  rw [h2]
  linarith
end GlobalTheory.PerronKernel
