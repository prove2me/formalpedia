-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.isLocal_iteratedLineDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:04:55.979477+00:00
-- url     : https://prove2.me/submissions/3dc7fc77-a6f0-496b-8b5b-9f6d16221d78

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
theorem _root_.solution {k : ℕ} (w : Fin k → E) :
    IsLocal (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) := fun _ _ _ hu ↦
  Distribution.TemperedDistribution.IsVanishingOn.iteratedLineDerivOp hu w
end GroundTheory.Automorphic.Sobolev
