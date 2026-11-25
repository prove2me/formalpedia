-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_iteratedDeriv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:05.766894+00:00
-- url     : https://prove2.me/submissions/2a0a566e-b3c1-4ece-a14c-63a8358df548

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_iteratedDeriv_of_contDiff
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_iteratedDeriv
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_deriv_mul

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
theorem _root_.solution {F ψ : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (p : ℕ) :
    ∫ u, iteratedDeriv p F u * ψ u = (-1) ^ p * ∫ u, F u * iteratedDeriv p ψ u := by
  induction p generalizing F with
  | zero => simp
  | succ p ih =>
    have hF' : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.1 hF).2
    rw [iteratedDeriv_succ', ih hF', pow_succ, mul_assoc]
    congr 1
    rw [integral_deriv_mul (hF.of_le (by simp))
      ((contDiff_iteratedDeriv_of_contDiff hψ p).of_le (by simp))
      (hasCompactSupport_iteratedDeriv hψc p), ← iteratedDeriv_succ]
    ring
end GroundTheory.Automorphic.LineKernel
