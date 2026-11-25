-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.bump_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:24.157076+00:00
-- url     : https://prove2.me/submissions/d27a4b5d-0f4f-4fb4-80fc-cf0942e3aa5e

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
theorem _root_.solution (x₀ : E) {r : ℝ} (hr : 0 < r) {x : E} (hx : x ∈ Metric.closedBall x₀ r) :
    bump x₀ hr x = 1 := by
  rw [bump_apply, (bumpR x₀ hr).one_of_mem_closedBall hx, Complex.ofReal_one]
end GroundTheory.Automorphic.Sobolev
