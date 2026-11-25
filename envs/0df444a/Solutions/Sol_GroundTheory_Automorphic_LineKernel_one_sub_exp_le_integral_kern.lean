-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.one_sub_exp_le_integral_kern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:49.079891+00:00
-- url     : https://prove2.me/submissions/26055344-ed80-4261-abef-9dada8c05e0f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_rem_le
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
theorem _root_.solution {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    1 - exp (-a * r) ≤ ∫ t, kern a r t := by
  have h1 := integral_kern_add_integral_rem ha hr
  have h2 := integral_rem_le ha.le hr
  linarith
end GroundTheory.Automorphic.LineKernel
