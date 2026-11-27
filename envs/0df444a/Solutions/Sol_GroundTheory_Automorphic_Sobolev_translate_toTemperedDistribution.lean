-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.translate_toTemperedDistribution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:34.412152+00:00
-- url     : https://prove2.me/submissions/9d57a1e7-8ac2-4601-a3f8-0f947537b379

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_translate_apply_apply
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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (h : E) (f : Lp F 2 (volume : Measure E)) (φ : 𝓢(E, ℂ)) :
    translate F h (f : 𝓢'(E, F)) φ = ∫ x, φ x • f (x - h) := by
  rw [translate_apply_apply, Lp.toTemperedDistribution_apply]
  have := (measurePreserving_add_right (volume : Measure E) h).integral_comp
    (measurableEmbedding_addRight h) (fun x ↦ φ x • f (x - h))
  simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add] at this ⊢
  rw [← this]
  congr 1; ext x
  rw [add_sub_cancel_right]
end GroundTheory.Automorphic.Sobolev
