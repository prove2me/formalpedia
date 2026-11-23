-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.smulLeftCLM_weight_fourier
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:55.147699+00:00
-- url     : https://prove2.me/submissions/166f517a-7f4e-405c-acd2-737fc87a02da

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
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s) :
    smulLeftCLM F (weight s) (𝓕 (SobolevSpace.toDistribution u)) =
      ((𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
  rw [← Lp.fourier_toTemperedDistribution_eq, SobolevSpace.toDistribution_bessel,
    besselPotential_eq_fourierMultiplierCLM, fourierMultiplierCLM_apply, fourier_fourierInv_eq]
end GroundTheory.Automorphic.Sobolev
