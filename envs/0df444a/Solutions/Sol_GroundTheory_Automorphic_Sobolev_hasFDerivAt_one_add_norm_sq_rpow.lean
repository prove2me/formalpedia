-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.hasFDerivAt_one_add_norm_sq_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:48:59.428705+00:00
-- url     : https://prove2.me/submissions/a9599f5f-3f0e-4dcf-8d63-53e2f4190b10

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (r : ℝ) (ζ : E) :
    HasFDerivAt (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (r / 2))
      ((r / 2 * (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1)) • (2 • innerSL ℝ ζ)) ζ := by
  have h1 : HasFDerivAt (fun x : E ↦ 1 + ‖x‖ ^ 2) (2 • innerSL ℝ ζ) ζ := by
    have := (hasFDerivAt_id ζ).norm_sq
    simpa using this.const_add 1
  exact h1.rpow_const (Or.inl (by positivity))
end GroundTheory.Automorphic.Sobolev
