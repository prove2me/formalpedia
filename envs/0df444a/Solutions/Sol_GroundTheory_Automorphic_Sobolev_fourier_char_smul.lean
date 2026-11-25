-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourier_char_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:17.455461+00:00
-- url     : https://prove2.me/submissions/e99cfba5-2c34-42e1-b18c-6efba531a7d8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich

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
theorem _root_.solution (χ : 𝓢(E, ℂ)) (η ξ : E) :
    𝓕 (fun x : E ↦ (𝐞 (inner ℝ x η) : ℂ) * χ x) ξ = (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) := by
  rw [Real.fourier_eq, SchwartzMap.fourier_coe, Real.fourier_eq]
  congr 1; ext x
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, inner_sub_right]
  congr 3; ring
end GroundTheory.Automorphic.Sobolev
