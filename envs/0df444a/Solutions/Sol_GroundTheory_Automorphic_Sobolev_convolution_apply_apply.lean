-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.convolution_apply_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:00:21.324741+00:00
-- url     : https://prove2.me/submissions/e0b86274-b300-40de-b0b7-7b15435a1897

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier

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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    convolution F ψ u φ =
      u (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ) φ) := rfl
end GroundTheory.Automorphic.Sobolev
