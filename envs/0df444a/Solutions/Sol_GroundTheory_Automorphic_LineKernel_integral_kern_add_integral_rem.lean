-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_kern_add_integral_rem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:55.46935+00:00
-- url     : https://prove2.me/submissions/e4b53d03-f1c4-46cb-a46c-dcb2300f1146

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_step_identity

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
    (∫ t, kern a r t) + ∫ t, rem a r t = 1 := by
  have h := step_identity ha hr (F := fun _ => (1 : ℂ)) (F' := fun _ => 0)
    (fun t => hasDerivAt_const t 1) continuous_const
  simp only [mul_zero, sub_zero, one_mul, integral_complex_ofReal] at h
  exact_mod_cast h.symm
end GroundTheory.Automorphic.LineKernel
