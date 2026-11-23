-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.cutoff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:43.186256+00:00
-- url     : https://prove2.me/submissions/f4c8dd38-126a-4b51-916b-73b8192e0c31

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
theorem _root_.solution (r t : ℝ) : 0 ≤ cutoff r t := by
  unfold cutoff; linarith [smoothTransition.le_one (t / r - 1)]
end GroundTheory.Automorphic.LineKernel
