-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.iteratedDeriv_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:11.878814+00:00
-- url     : https://prove2.me/submissions/7685e1f8-46f6-472d-90bd-92b37c754793

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
theorem _root_.solution {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    iteratedDeriv m (fun t => (f t : ℂ)) = fun t => ((iteratedDeriv m f t : ℝ) : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact ((hasDerivAt_iteratedDeriv hf m t).ofReal_comp).deriv
end GroundTheory.Automorphic.LineKernel
