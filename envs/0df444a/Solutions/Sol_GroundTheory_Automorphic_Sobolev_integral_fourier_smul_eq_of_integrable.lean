-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.integral_fourier_smul_eq_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:11.468634+00:00
-- url     : https://prove2.me/submissions/199a5b5f-dda1-453f-9926-7a223381ab24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev

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
variable {m : E → ℂ} {C s t : ℝ}
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (φ : 𝓢(E, ℂ)) {g : E → F}
    (hg : Integrable g (volume : Measure E)) :
    ∫ ξ, 𝓕 φ ξ • g ξ = ∫ x, φ x • 𝓕 g x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ E)
    Real.continuous_fourierChar continuous_inner φ.integrable hg
end GroundTheory.Automorphic.Sobolev
