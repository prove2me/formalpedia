-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.support_Kc_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:53.208795+00:00
-- url     : https://prove2.me/submissions/97610bf7-d769-49f6-be9d-4cc5dd060d42

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_kern_subset


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
theorem _root_.solution (n : ℕ) : support (Kc a r n) ⊆ Icc 0 (Rs r n) := by
  induction n with
  | zero =>
    show support (kern (a 0) (r 0)) ⊆ _
    simpa [Rs] using support_kern_subset (hr 0)
  | succ n ih =>
    refine (support_convolution_subset (mul ℝ ℝ)).trans ?_
    refine (Set.add_subset_add ih (support_kern_subset (hr _))).trans ?_
    refine (Set.Icc_add_Icc_subset _ _ _ _).trans (Icc_subset_Icc (by simp) (le_of_eq ?_))
    simp [Rs, Finset.sum_range_succ]
end GroundTheory.Automorphic.LineKernel
