-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.convolution_eq_fourierMultiplierCLM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:25.341355+00:00
-- url     : https://prove2.me/submissions/7a239e94-478e-4462-9ac4-ef57a2bc1d7d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_convolution_apply_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_convolution_reflect_eq

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
theorem _root_.solution (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) :
    convolution F ψ u = fourierMultiplierCLM F ⇑(𝓕 ψ : 𝓢(E, ℂ)) u := by
  ext φ
  rw [convolution_apply_apply, convolution_reflect_eq, fourierMultiplierCLM_apply_apply]
end GroundTheory.Automorphic.Sobolev
