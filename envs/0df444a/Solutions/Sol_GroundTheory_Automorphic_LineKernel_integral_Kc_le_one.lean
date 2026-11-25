-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_Kc_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:24.501523+00:00
-- url     : https://prove2.me/submissions/cf4d4f8e-e365-47a6-99e2-8267edd4a532

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_Kc_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_Kc__49dcd9
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_kern
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_kern_le_one


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
theorem _root_.solution (n : ℕ) : ∫ t, Kc a r n t ≤ 1 := by
  induction n with
  | zero => exact integral_kern_le_one (ha 0) (hr 0)
  | succ n ih =>
    simp only [Kc]
    rw [integral_convolution (mul ℝ ℝ) (integrable_Kc ha hr n) (integrable_kern (ha _).le (hr _)),
      mul_apply']
    have h1 : 0 ≤ ∫ t, Kc a r n t := integral_nonneg (Kc_nonneg ha hr n)
    have h2 := integral_kern_le_one (ha (n + 1)) (hr (n + 1))
    nlinarith
end GroundTheory.Automorphic.LineKernel
