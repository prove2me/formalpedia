-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.cutoff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:54.620798+00:00
-- url     : https://prove2.me/submissions/7d490cf3-fb42-400d-844e-a9156297954b

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
theorem _root_.solution {r t : ℝ} (hr : 0 < r) (ht : 2 * r ≤ t) : cutoff r t = 0 := by
  unfold cutoff
  rw [smoothTransition.one_of_one_le, sub_self]
  rw [le_sub_iff_add_le, le_div_iff₀ hr]; linarith
end GroundTheory.Automorphic.LineKernel
