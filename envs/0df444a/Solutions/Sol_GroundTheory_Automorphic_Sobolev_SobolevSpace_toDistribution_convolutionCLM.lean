-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:30.144799+00:00
-- url     : https://prove2.me/submissions/01805ca6-3e26-4ec9-9ec6-8f7e1ec065c7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_convolution_eq_fourierMultiplierCLM

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
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}
namespace GroundTheory.Automorphic.Sobolev.SobolevSpace
theorem _root_.solution (ψ : 𝓢(E, ℂ)) (u : SobolevSpace E F s) :
    toDistribution (convolutionCLM ψ u) = convolution F ψ (toDistribution u) := by
  rw [convolution_eq_fourierMultiplierCLM]; rfl
end GroundTheory.Automorphic.Sobolev.SobolevSpace
