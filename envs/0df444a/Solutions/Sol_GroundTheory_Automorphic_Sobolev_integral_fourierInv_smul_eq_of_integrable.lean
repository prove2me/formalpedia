-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.integral_fourierInv_smul_eq_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:00:25.435205+00:00
-- url     : https://prove2.me/submissions/58c26929-c9c8-4112-9260-8dd4073745e1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (φ : 𝓢(E, ℂ)) {g : E → F}
    (hg : Integrable g (volume : Measure E)) :
    ∫ ξ, 𝓕⁻ (φ : E → ℂ) ξ • g ξ = ∫ x, φ x • 𝓕⁻ g x := by
  have hflip : (-innerₗ E).flip = -innerₗ E := by
    ext x y; simp [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ E)
    Real.continuous_fourierChar
    (by simp only [LinearMap.neg_apply, innerₗ_apply_apply]; fun_prop)
    (φ.integrable (μ := (volume : Measure E))) hg
  rw [hflip] at h
  exact h
end GroundTheory.Automorphic.Sobolev
