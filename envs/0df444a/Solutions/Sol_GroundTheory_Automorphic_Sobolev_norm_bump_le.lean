-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_bump_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:27:53.20265+00:00
-- url     : https://prove2.me/submissions/48416c6d-b6be-4697-81c5-c0fbf6fbad62

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_bump_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (x₀ : E) {r : ℝ} (hr : 0 < r) (x : E) : ‖bump x₀ hr x‖ ≤ 1 := by
  rw [bump_apply, Complex.norm_real, Real.norm_of_nonneg (bumpR x₀ hr).nonneg]
  exact (bumpR x₀ hr).le_one
end GroundTheory.Automorphic.Sobolev
