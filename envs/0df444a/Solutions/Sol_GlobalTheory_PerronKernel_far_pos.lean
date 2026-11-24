-- Prove2me | solution 1 for GlobalTheory.PerronKernel.far_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:09.86588+00:00
-- url     : https://prove2.me/submissions/673f1e92-87e5-4e97-9cf6-70f1f446dfbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Theorems.Thm_GlobalTheory_PerronKernel_vbound
import Theorems.Thm_GlobalTheory_PerronKernel_hbound
import Theorems.Thm_GlobalTheory_PerronKernel_rect_left
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
theorem _root_.solution {L c T : ℝ} (hL : 0 < L) (hc : 0 < c) (hT : 0 < T) :
    ‖(∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)) - 2 * Real.pi‖
      ≤ 2 * Real.exp (L * c) / (T * |L|) := by
  apply le_of_forall_large (c := c) hc (K := 2 * T) (by positivity)
  intro U hU
  have hU0 : 0 < U := lt_of_lt_of_le hc hU
  have hR := rect_left L (a := -U) (b := c) (T := T) (by linarith) hc hT
  have h3 := norm_le_three
    (x := (∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)) - 2 * Real.pi)
    (p := ∫ x in (-U)..c, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    (q := ∫ x in (-U)..c, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
    (r := ∫ t in (-T)..T, cexp (L * (((-U : ℝ) : ℂ) + t * I)) / (((-U : ℝ) : ℂ) + t * I)) (Or.inr (by linear_combination hR))
  have hLT : 0 < L * T := mul_pos hL hT
  have key : ∀ s : ℝ, |s| = T → (Real.exp (L * c) - Real.exp (L * -U)) / (L * |s|)
      ≤ Real.exp (L * c) / (T * |L|) := by
    intro s hs
    rw [hs, abs_of_pos hL, mul_comm T L]
    exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (L * -U)]) hLT.le
  have hUc : -U ≤ c := by linarith
  have hp := (hbound hL.ne' (t := -T) (neg_ne_zero.mpr hT.ne') hUc).trans
    (key (-T) (by rw [abs_neg, abs_of_pos hT]))
  have hq := (hbound hL.ne' (t := T) hT.ne' hUc).trans (key T (abs_of_pos hT))
  have hexp : Real.exp (L * -U) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hr : Real.exp (L * -U) / |-U| * (2 * T) ≤ 2 * T / U := by
    rw [abs_neg, abs_of_pos hU0, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hU0.le
  have hr' := (vbound L (σ := -U) (by linarith) hT.le).trans hr
  have h2 : 2 * Real.exp (L * c) / (T * |L|) =
      Real.exp (L * c) / (T * |L|) + Real.exp (L * c) / (T * |L|) := by ring
  rw [h2]
  linarith
end GlobalTheory.PerronKernel
