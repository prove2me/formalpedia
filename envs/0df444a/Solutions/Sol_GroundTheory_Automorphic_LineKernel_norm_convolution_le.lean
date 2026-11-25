-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.norm_convolution_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:17.395058+00:00
-- url     : https://prove2.me/submissions/b4ee2062-b978-4b90-90ff-6937859f7b27

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds

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
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {K g : ℝ → ℂ} {B : ℝ} (hK : Integrable K) (hg : ∀ t, ‖g t‖ ≤ B)
    (x : ℝ) : ‖(K ⋆[mul ℂ ℂ] g) x‖ ≤ B * ∫ t, ‖K t‖ := by
  rw [convolution_mul, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun t => norm_nonneg _) (hK.norm.const_mul B)
    (Eventually.of_forall fun t => ?_))
  simp only [norm_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hg _) (norm_nonneg _)
end GroundTheory.Automorphic.LineKernel
