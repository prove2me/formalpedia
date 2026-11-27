-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_diffQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:24.626733+00:00
-- url     : https://prove2.me/submissions/858c28a9-d59c-4653-a5f1-0c47b4b40edf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_translate_eq_fourierMultiplierCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



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
theorem _root_.solution (v : E) (t : ℝ) (u : SobolevSpace E F s) :
    toDistribution (diffQuot v t u) =
      ((t⁻¹ : ℝ) : ℂ) • (translate F (-(t • v)) (toDistribution u) - toDistribution u) := by
  rw [diffQuot, toDistribution_multiplier, translate_eq_fourierMultiplierCLM, neg_neg]
  have hsub : (dqSymbol v t : E → ℂ) = ((t⁻¹ : ℝ) : ℂ) • (expChar (t • v) - fun _ ↦ (1 : ℂ)) := by
    funext ξ; simp [dqSymbol]
  rw [hsub, fourierMultiplierCLM_smul ((expChar_hasTemperateGrowth _).sub
    (Function.HasTemperateGrowth.const 1)), smul_apply]
  congr 1
  rw [fourierMultiplierCLM_apply, fourierMultiplierCLM_apply,
    smulLeftCLM_sub (expChar_hasTemperateGrowth _) (Function.HasTemperateGrowth.const 1),
    sub_apply, smulLeftCLM_const, one_smul, ← fourierInvCLM_apply (R := ℂ), map_sub,
    fourierInvCLM_apply, fourierInvCLM_apply, FourierTransform.fourierInv_fourier_eq]
end GroundTheory.Automorphic.Sobolev.SobolevSpace
