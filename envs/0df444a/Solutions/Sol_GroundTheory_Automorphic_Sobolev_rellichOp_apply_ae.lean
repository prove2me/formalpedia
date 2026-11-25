-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.rellichOp_apply_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:23.033072+00:00
-- url     : https://prove2.me/submissions/114497f2-8119-4211-b8da-248a8dda2b5a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Theorems.Thm_GroundTheory_Automorphic_L2Kernel_kernelOp_toLp_apply_ae


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
variable {s N : ℝ} (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (hN : (Module.finrank ℝ E : ℝ) < 2 * N)
    (G : Lp ℂ 2 (volume : Measure E)) :
    rellichOp (s := s) χ hN G =ᵐ[volume] fun ξ ↦ ∫ η, rellichKernel s N χ (ξ, η) * G η :=
  L2Kernel.kernelOp_toLp_apply_ae (memLp_rellichKernel χ hN) G
end GroundTheory.Automorphic.Sobolev
