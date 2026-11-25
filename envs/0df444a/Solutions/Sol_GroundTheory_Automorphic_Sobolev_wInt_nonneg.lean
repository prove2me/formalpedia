-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.wInt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:03:33.048647+00:00
-- url     : https://prove2.me/submissions/26acce8b-c966-4dac-a6ef-6c7969436e15

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (c : ℝ) (ψ : 𝓢(E, ℂ)) : 0 ≤ wInt c ψ :=
  integral_nonneg fun ζ ↦ by positivity
end GroundTheory.Automorphic.Sobolev
