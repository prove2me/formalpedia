-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.summable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:00.996522+00:00
-- url     : https://prove2.me/submissions/9ebf7955-d5eb-47ab-bf16-eeb40f0a147e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine

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
variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (k : ℕ) : Summable (majorant hε hg k) := by
  refine (summable_geometric_two).add (summable_of_ne_finset_zero (s := Finset.range (k + 1))
    fun j hj => ?_)
  rw [if_neg]; rw [Finset.mem_range] at hj; omega
end GroundTheory.Automorphic.LineKernel
