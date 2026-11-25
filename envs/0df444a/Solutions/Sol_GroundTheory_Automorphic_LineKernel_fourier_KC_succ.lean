-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.fourier_KC_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:29:35.900574+00:00
-- url     : https://prove2.me/submissions/cfb35a77-8974-4a36-a98f-e90bae1c6e6f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_KC_succ
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_KC
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_kern


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
theorem _root_.solution (n : ℕ) (ξ : ℝ) :
    𝓕 (KC a r (n + 1)) ξ = 𝓕 (KC a r n) ξ * khat (a (n + 1)) (r (n + 1)) ξ := by
  rw [KC_succ ha hr n, fourier_mul_convolution_eq (f₂ := kC a r (n + 1)) (integrable_KC ha hr n)
    (integrable_kern (ha (n + 1)).le (hr (n + 1))).ofReal]
  rfl
end GroundTheory.Automorphic.LineKernel
