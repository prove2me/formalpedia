-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.bump_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:29.517241+00:00
-- url     : https://prove2.me/submissions/0e706dbb-2113-42a8-b629-d3393bd5849e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_tsupport_bump

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
theorem _root_.solution (x₀ : E) {r : ℝ} (hr : 0 < r) {x : E} (hx : x ∉ Metric.closedBall x₀ (2 * r)) :
    bump x₀ hr x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_bump x₀ hr h)
end GroundTheory.Automorphic.Sobolev
