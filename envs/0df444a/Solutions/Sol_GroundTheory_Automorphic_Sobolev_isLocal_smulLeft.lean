-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.isLocal_smulLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:04:59.336381+00:00
-- url     : https://prove2.me/submissions/4fdf06f9-1632-4030-9c05-4267456b9479

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
theorem _root_.solution {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    IsLocal (smulLeftCLM ℂ g) := fun _ _ _ hu ↦
  Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM hu hg
end GroundTheory.Automorphic.Sobolev
