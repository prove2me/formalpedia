-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.isVanishingOn_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:05:02.662815+00:00
-- url     : https://prove2.me/submissions/a6fa6e20-be49-41de-828a-2d918143e48b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators

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
theorem _root_.solution {u : 𝓢'(E, ℂ)} {U : Set E} (hu : Distribution.IsVanishingOn u U) :
    Distribution.IsVanishingOn (-u) U := fun φ hφ ↦ by
  rw [neg_apply, hu φ hφ, neg_zero]
end GroundTheory.Automorphic.Sobolev
