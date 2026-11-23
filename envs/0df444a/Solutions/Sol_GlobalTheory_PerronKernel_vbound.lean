-- Prove2me | solution 1 for GlobalTheory.PerronKernel.vbound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:38.28669+00:00
-- url     : https://prove2.me/submissions/2316a672-3b7a-4d95-92d4-df178e90c460

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
theorem _root_.solution (L : ℝ) {σ T : ℝ} (h : σ ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, cexp (L * ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I)‖
      ≤ Real.exp (L * σ) / |σ| * (2 * T) := by
  have hb : ∀ t ∈ Set.uIoc (-T) T,
      ‖cexp (L * ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I)‖ ≤ Real.exp (L * σ) / |σ| := by
    intro t _
    rw [norm_div, norm_exp]
    apply div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.mpr h)
    simpa using Complex.abs_re_le_norm ((σ : ℂ) + t * I)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by linarith)]] at this
end GlobalTheory.PerronKernel
