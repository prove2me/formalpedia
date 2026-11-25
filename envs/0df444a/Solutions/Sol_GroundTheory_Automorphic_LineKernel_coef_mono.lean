-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.coef_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:24.29968+00:00
-- url     : https://prove2.me/submissions/dfaf3e10-644e-43fc-b0a5-23b3ee041bf4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_nonneg


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
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (n p : ℕ) : coef a n p ≤ coef a (n + 1) p := by
  cases p with
  | zero => simp [coef]
  | succ p => simp only [coef]; linarith [div_nonneg (coef_nonneg ha n p) (ha n).le]
end GroundTheory.Automorphic.LineKernel
