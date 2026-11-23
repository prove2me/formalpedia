-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.contDiff_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:54.538837+00:00
-- url     : https://prove2.me/submissions/8926ab03-bfe0-4a7a-ae9e-00e1aea71dc2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (r : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoff r) := by
  unfold cutoff
  exact contDiff_const.sub (smoothTransition.contDiff.comp
    ((contDiff_id.div_const r).sub contDiff_const))
end GroundTheory.Automorphic.LineKernel
