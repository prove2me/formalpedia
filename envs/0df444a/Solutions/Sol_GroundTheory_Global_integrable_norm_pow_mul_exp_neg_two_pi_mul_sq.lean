-- Prove2me | solution 1 for GroundTheory.Global.integrable_norm_pow_mul_exp_neg_two_pi_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:58.017032+00:00
-- url     : https://prove2.me/submissions/627f7e91-d8d3-4cf0-ba2c-fd6f2aabc689

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.traceFormℂ_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform ENNReal
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (k : ℕ) :
    Integrable (fun z : ℂ ↦ ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
  have h := (integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun y : ℝ ↦ y ^ k * Real.exp (-(2 * π) * y ^ 2))).2
  refine h ?_
  rw [Complex.finrank_real_complex]
  have h2 := integrableOn_rpow_mul_exp_neg_mul_sq (b := 2 * π) (by positivity)
    (s := ((k + 1 : ℕ) : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) (k + 1); linarith)
  refine h2.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, smul_eq_mul]
  ring
end GroundTheory.Global
