-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_norm_KC_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:25.700651+00:00
-- url     : https://prove2.me/submissions/bd329e07-ec12-40ae-830d-8554b3575232

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_Kc_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_Kc_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (n : ℕ) : ∫ t, ‖KC a r n t‖ ≤ 1 := by
  have : (fun t => ‖KC a r n t‖) = Kc a r n := by
    funext t; simp [KC, Complex.norm_real, abs_of_nonneg (Kc_nonneg ha hr n t)]
  rw [this]; exact integral_Kc_le_one ha hr n
end GroundTheory.Automorphic.LineKernel
