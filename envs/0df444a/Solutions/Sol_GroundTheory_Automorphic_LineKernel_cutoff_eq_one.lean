-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.cutoff_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:36.737225+00:00
-- url     : https://prove2.me/submissions/5cd928d1-81d5-4eb4-ba3a-ac603fec8a93

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
theorem _root_.solution {r t : ℝ} (hr : 0 < r) (ht : t ≤ r) : cutoff r t = 1 := by
  unfold cutoff
  rw [smoothTransition.zero_of_nonpos, sub_zero]
  rw [sub_nonpos, div_le_one hr]; exact ht
end GroundTheory.Automorphic.LineKernel
