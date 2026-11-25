-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.one_le_sqrt_one_add_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:01:53.926318+00:00
-- url     : https://prove2.me/submissions/b6703c43-1aca-4dc9-8628-d977b0f68a10

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal

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
theorem _root_.solution (ξ : E) : 1 ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := by
  rw [Real.one_le_sqrt]; nlinarith [sq_nonneg ‖ξ‖]
end GroundTheory.Automorphic.Sobolev
