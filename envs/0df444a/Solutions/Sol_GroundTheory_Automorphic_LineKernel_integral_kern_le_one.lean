-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_kern_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:55.993874+00:00
-- url     : https://prove2.me/submissions/2cba2bcc-bfbc-48ac-995b-28412f00c629

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_rem_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_kern_add_integral_rem

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
theorem _root_.solution {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : ∫ t, kern a r t ≤ 1 := by
  have h1 := integral_kern_add_integral_rem ha hr
  have h2 : 0 ≤ ∫ t, rem a r t := integral_nonneg (rem_nonneg hr)
  linarith
end GroundTheory.Automorphic.LineKernel
