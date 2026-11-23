-- Prove2me | solution 1 for GlobalTheory.GaussWidths.exists_schwartz_gauss_width
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:24.354687+00:00
-- url     : https://prove2.me/submissions/67dac5cb-7398-4100-8d82-bbf026358df8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussWidths
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory.GaussWidths
theorem _root_.solution (c : ℝ) (hc : 0 < c) :
    ∃ g : SchwartzMap E ℂ, ∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  set t : ℝ := Real.sqrt (c / Real.pi) with ht_def
  have ht : t ≠ 0 := (Real.sqrt_pos.2 (div_pos hc Real.pi_pos)).ne'
  have ht2 : t ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc Real.pi_pos).le
  let e : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E t ht).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (GroundTheory.Global.gaussianSchwartz E), fun y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
  congr 1
  have hey : e y = t • y := rfl
  rw [hey, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ht2]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
end GlobalTheory.GaussWidths
