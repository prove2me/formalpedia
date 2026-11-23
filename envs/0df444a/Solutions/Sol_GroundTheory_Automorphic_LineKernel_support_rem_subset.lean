-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.support_rem_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:02.276546+00:00
-- url     : https://prove2.me/submissions/a26400a9-caa5-415a-9b4c-2c7c6bcca8de

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_rem_eq_zero

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
theorem _root_.solution {a r : ℝ} (hr : 0 < r) : support (rem a r) ⊆ Icc r (2 * r) := by
  intro t ht; by_contra h; exact ht (rem_eq_zero hr h)
end GroundTheory.Automorphic.LineKernel
