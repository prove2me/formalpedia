-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.contDiff_deriv_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:47.542945+00:00
-- url     : https://prove2.me/submissions/a73221a0-7e7e-4857-9c6e-93e7b00da635

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_cutoff

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
theorem _root_.solution (r : ℝ) : ContDiff ℝ ∞ (deriv (cutoff r)) :=
  (contDiff_infty_iff_deriv.1 (contDiff_cutoff r)).2
end GroundTheory.Automorphic.LineKernel
