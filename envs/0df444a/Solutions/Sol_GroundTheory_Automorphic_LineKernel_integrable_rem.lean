-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integrable_rem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:56.114421+00:00
-- url     : https://prove2.me/submissions/496a8c48-00b6-4412-b5d6-d318fa02e535

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_rem
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_rem

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
theorem _root_.solution {a r : ℝ} (hr : 0 < r) : Integrable (rem a r) :=
  (contDiff_rem a r).continuous.integrable_of_hasCompactSupport (hasCompactSupport_rem hr)
end GroundTheory.Automorphic.LineKernel
