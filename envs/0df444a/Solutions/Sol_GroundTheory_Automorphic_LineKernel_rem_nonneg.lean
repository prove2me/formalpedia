-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.rem_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:58.229748+00:00
-- url     : https://prove2.me/submissions/67d394b2-caec-4515-9359-bac69a6b7410

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_deriv_cutoff_nonpos

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
theorem _root_.solution {a r : ℝ} (hr : 0 < r) (t : ℝ) : 0 ≤ rem a r t := by
  unfold rem
  have := deriv_cutoff_nonpos hr t
  nlinarith [exp_pos (-a * t)]
end GroundTheory.Automorphic.LineKernel
