-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.support_kern_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:09.196904+00:00
-- url     : https://prove2.me/submissions/73d2e018-5d69-4aad-8cdf-06c05d61ae0d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_eq_zero_of_neg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_eq_zero_of_ge

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
theorem _root_.solution {a r : ℝ} (hr : 0 < r) : support (kern a r) ⊆ Icc 0 (2 * r) := by
  intro t ht
  by_contra h
  rcases not_and_or.1 h with h | h
  · exact ht (kern_eq_zero_of_neg (not_le.1 h))
  · exact ht (kern_eq_zero_of_ge hr (not_le.1 h).le)
end GroundTheory.Automorphic.LineKernel
