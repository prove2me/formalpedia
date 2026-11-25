-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.norm_fourier_KC_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:12.670533+00:00
-- url     : https://prove2.me/submissions/aabd7e1a-5eeb-48d1-bdbe-64e44daedd2d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_fourier_KC_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_fourier_KC_succ
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_khat_le_one


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
theorem _root_.solution (n : ℕ) (ξ : ℝ) : ‖𝓕 (KC a r n) ξ‖ ≤ 1 := by
  induction n with
  | zero => rw [fourier_KC_zero ha hr]; exact norm_khat_le_one (ha 0) (hr 0) ξ
  | succ n ih =>
    rw [fourier_KC_succ ha hr, norm_mul]
    exact mul_le_one₀ ih (norm_nonneg _) (norm_khat_le_one (ha _) (hr _) ξ)
end GroundTheory.Automorphic.LineKernel
