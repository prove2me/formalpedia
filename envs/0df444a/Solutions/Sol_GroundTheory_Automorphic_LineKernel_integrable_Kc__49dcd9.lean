-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integrable_Kc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:12:52.616555+00:00
-- url     : https://prove2.me/submissions/525280e0-ded6-4732-8f48-9ec5c1cb95f3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
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
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (n : ℕ) : Integrable (Kc a r n) := by
  induction n with
  | zero => exact integrable_kern (ha 0).le (hr 0)
  | succ n ih => exact ih.integrable_convolution (mul ℝ ℝ) (integrable_kern (ha _).le (hr _))
end GroundTheory.Automorphic.LineKernel
