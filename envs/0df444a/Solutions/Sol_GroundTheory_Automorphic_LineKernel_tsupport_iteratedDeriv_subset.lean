-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.tsupport_iteratedDeriv_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:24.561048+00:00
-- url     : https://prove2.me/submissions/45862bab-662a-4e60-be94-615a8b157b77

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds

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
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (m : ℕ) : tsupport (iteratedDeriv m f) ⊆ tsupport f := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih
end GroundTheory.Automorphic.LineKernel
