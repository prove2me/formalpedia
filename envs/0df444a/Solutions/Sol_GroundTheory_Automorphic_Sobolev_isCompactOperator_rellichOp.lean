-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.isCompactOperator_rellichOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:17.981733+00:00
-- url     : https://prove2.me/submissions/075b9139-8965-470b-b0d9-77fbe19b42c0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_isCompactOperator
import Theorems.Thm_GroundTheory_Automorphic_L2Kernel_kernelOp_isHilbertSchmidt


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
theorem _root_.solution (hN : (Module.finrank ℝ E : ℝ) < 2 * N) :
    IsCompactOperator (rellichOp (s := s) χ hN) :=
  (L2Kernel.kernelOp_isHilbertSchmidt _).isCompactOperator
end GroundTheory.Automorphic.Sobolev
