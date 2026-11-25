-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.hasDerivAt_opT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:29.859798+00:00
-- url     : https://prove2.me/submissions/552e0f22-f24e-4423-b041-abde8b2bc3fa

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasDerivAt_iteratedDeriv

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
theorem _root_.solution (a : ℕ → ℝ) (n : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (x : ℝ) :
    HasDerivAt (opT a n F)
      (∑ p ∈ Finset.range (n + 1), sc a n p * iteratedDeriv (p + 1) F x) x := by
  have := HasDerivAt.sum (u := Finset.range (n + 1)) (A := fun p y => sc a n p * iteratedDeriv p F y)
    (fun p _ => (hasDerivAt_iteratedDeriv hF p x).const_mul (sc a n p))
  have e : opT a n F = ∑ i ∈ Finset.range (n + 1), fun y => sc a n i * iteratedDeriv i F y := by
    funext y; simp [opT, Finset.sum_apply]
  rw [e]; exact this
end GroundTheory.Automorphic.LineKernel
