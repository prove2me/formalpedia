-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_diffQuot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:20.724967+00:00
-- url     : https://prove2.me/submissions/38d9be6b-b04c-4477-bd9f-0077adeb3170

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dqSymbol_bound
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_multiplier_apply_le
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
theorem _root_.solution (v : E) (t : ℝ) (u : SobolevSpace E F (s + 1)) :
    ‖diffQuot v t (inclusion (le_add_of_nonneg_right zero_le_one) u)‖ ≤ 2 * Real.pi * ‖v‖ * ‖u‖ := by
  have h : diffQuot v t (inclusion (le_add_of_nonneg_right zero_le_one) u) =
      multiplier (dqSymbol_hasTemperateGrowth v t) (dqSymbol_bound (s := s) v t) u := by
    apply toDistribution_injective
    simp [diffQuot]
  rw [h]
  exact norm_multiplier_apply_le _ _ u
end GroundTheory.Automorphic.Sobolev.SobolevSpace
