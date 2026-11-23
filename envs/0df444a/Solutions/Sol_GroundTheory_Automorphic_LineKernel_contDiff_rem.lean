-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.contDiff_rem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:35.995031+00:00
-- url     : https://prove2.me/submissions/589bb270-167c-4f72-a48f-f3fb8aa51e2b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_deriv_cutoff

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
theorem _root_.solution (a r : ℝ) : ContDiff ℝ ∞ (rem a r) := by
  unfold rem
  exact ((contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul (contDiff_deriv_cutoff r)).neg
end GroundTheory.Automorphic.LineKernel
