-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.norm_fourier_KC_succ_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:08.640324+00:00
-- url     : https://prove2.me/submissions/47945f49-0822-40e7-acdd-8bcdb63c8b44

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_fourier_KC_succ
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_fourier_KC_le_one
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_khat_sub_one_le


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
    ‖𝓕 (KC a r (n + 1)) ξ - 𝓕 (KC a r n) ξ‖ ≤
      4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1)) := by
  rw [fourier_KC_succ ha hr, ← mul_sub_one, norm_mul]
  calc ‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ - 1‖
      ≤ 1 * (4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1))) :=
        mul_le_mul (norm_fourier_KC_le_one ha hr n ξ) (norm_khat_sub_one_le (ha _) (hr _) ξ)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _
end GroundTheory.Automorphic.LineKernel
