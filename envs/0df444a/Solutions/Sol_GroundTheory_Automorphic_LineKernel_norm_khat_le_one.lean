-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.norm_khat_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:25.252993+00:00
-- url     : https://prove2.me/submissions/88ab95d7-f2be-4d9a-919e-1fda5d380fa6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_kern_le_one
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_khat_eq

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
theorem _root_.solution {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (ξ : ℝ) : ‖khat a r ξ‖ ≤ 1 := by
  rw [khat_eq]
  refine (norm_integral_le_integral_norm _).trans ?_
  have : (fun t => ‖Complex.exp (↑(-2 * π * t * ξ) * Complex.I) * (kern a r t : ℂ)‖) =
      fun t => kern a r t := by
    funext t
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (kern_nonneg ha.le r t)]
  rw [this]; exact integral_kern_le_one ha hr
end GroundTheory.Automorphic.LineKernel
