-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_deriv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:31.890012+00:00
-- url     : https://prove2.me/submissions/1db21184-4203-4e1c-b221-defd48c357af

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {F ψ : ℝ → ℂ} (hF : ContDiff ℝ 1 F) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) : ∫ u, deriv F u * ψ u = -∫ u, F u * deriv ψ u := by
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := F) (v := ψ) (u' := deriv F)
    (v' := deriv ψ) (fun x _ => (hFd x).hasDerivAt) (fun x _ => (hψd x).hasDerivAt)
    ((hF.continuous.mul (hψ.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      hψc.deriv.mul_left)
    (((hF.continuous_deriv le_rfl).mul hψ.continuous).integrable_of_hasCompactSupport
      hψc.mul_left)
    ((hF.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)
  rw [h, neg_neg]
end GroundTheory.Automorphic.LineKernel
