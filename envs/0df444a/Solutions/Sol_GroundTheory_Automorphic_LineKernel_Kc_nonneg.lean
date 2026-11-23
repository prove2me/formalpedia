-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.Kc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:53.942115+00:00
-- url     : https://prove2.me/submissions/8dcbf7ae-9943-4a06-a676-f91488f79ad7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_nonneg


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
theorem _root_.solution (n : ℕ) (t : ℝ) : 0 ≤ Kc a r n t := by
  induction n generalizing t with
  | zero => exact kern_nonneg (ha 0).le _ _
  | succ n ih =>
    simp only [Kc]; rw [convolution_mul]
    exact integral_nonneg fun s => mul_nonneg (ih s) (kern_nonneg (ha _).le _ _)
end GroundTheory.Automorphic.LineKernel
