-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.hasCompactSupport_rem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:19.643447+00:00
-- url     : https://prove2.me/submissions/f3059a72-c0ee-4122-8dc9-09f6b44dda31

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_rem_subset

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
theorem _root_.solution {a r : ℝ} (hr : 0 < r) : HasCompactSupport (rem a r) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_rem_subset hr)
end GroundTheory.Automorphic.LineKernel
