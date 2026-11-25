-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.measurable_weight_mul_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:49.427058+00:00
-- url     : https://prove2.me/submissions/3b3868ae-d41c-48ff-a06e-8e7b9b5bc68d

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
theorem _root_.solution (r : ℝ) (φ : 𝓢(E, ℂ)) :
    Measurable fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ :=
  ((weight_hasTemperateGrowth (E := E) r).1.continuous.mul (𝓕 φ : 𝓢(E, ℂ)).continuous).measurable
end GroundTheory.Automorphic.Sobolev
