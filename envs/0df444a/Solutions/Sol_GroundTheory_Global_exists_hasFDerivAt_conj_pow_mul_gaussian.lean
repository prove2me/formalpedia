-- Prove2me | solution 1 for GroundTheory.Global.exists_hasFDerivAt_conj_pow_mul_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:19.543633+00:00
-- url     : https://prove2.me/submissions/bc85a992-6ba2-4d71-9f3c-bdc2d07d387b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Theorems.Thm_GroundTheory_Global_cexp_neg_two_pi_norm_sq
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (n : ℕ) (w : ℂ) :
    ∃ D : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun w : ℂ ↦ conj w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) D w ∧
      D 1 - I * D I = -4 * π * (conj w ^ (n + 1) * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  simp only [cexp_neg_two_pi_norm_sq]
  have hc : HasFDerivAt (fun w : ℂ ↦ conj w) (conjCLE : ℂ →L[ℝ] ℂ) w :=
    (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have hid : HasFDerivAt (fun w : ℂ ↦ w) (ContinuousLinearMap.id ℝ ℂ) w := hasFDerivAt_id w
  have hq := (hid.fun_mul hc).const_mul (-2 * π : ℂ)
  have hexp := hq.cexp
  have hp := hc.pow n
  refine ⟨_, hp.fun_mul hexp, ?_⟩
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_id', id, ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_one,
    conj_I, smul_eq_mul, nsmul_eq_mul]
  rw [pow_succ]
  linear_combination (conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * (-2 * π) * (-w) +
    Complex.exp (-2 * π * (w * conj w)) * (n * conj w ^ (n - 1)) +
    2 * conj w * conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * π -
    4 * conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * π * w) * I_sq
end GroundTheory.Global
