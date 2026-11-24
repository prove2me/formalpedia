-- Prove2me | solution 1 for GlobalTheory.NarrowGauss.gauss_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:34.944602+00:00
-- url     : https://prove2.me/submissions/94bab74e-7a5e-44b3-8933-34e8d3d458fb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartzStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NarrowGaussConvolutionDense
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
open GlobalTheory GlobalTheory.NarrowGauss
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory.NarrowGauss
theorem _root_.solution (c : ℝ) (hc : 0 < c) (x : E) :
    gauss c hc x = Complex.exp (-(c : ℂ) * ‖x‖ ^ 2) := by
  rw [gauss, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply]
  have h : -Real.pi * ‖(LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv x‖ ^ 2
      = -c * ‖x‖ ^ 2 := by
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (div_pos hc Real.pi_pos).le]
    field_simp
  rw [h, Complex.ofReal_exp]
  push_cast
  ring_nf
end GlobalTheory.NarrowGauss
