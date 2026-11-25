-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_dqSymbol_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:16.136124+00:00
-- url     : https://prove2.me/submissions/7c7557b3-72d3-492a-bdfe-982058f6e59b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_expChar_sub_one_le
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
theorem _root_.solution (v : E) (t : ℝ) (ξ : E) : ‖dqSymbol v t ξ‖ ≤ 2 * Real.pi * |inner ℝ ξ v| := by
  rw [dqSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_ne t 0 with rfl | ht
  · simp; positivity
  calc |t⁻¹| * ‖expChar (t • v) ξ - 1‖ ≤ |t⁻¹| * (2 * Real.pi * |inner ℝ ξ (t • v)|) := by
        gcongr; exact norm_expChar_sub_one_le _ _
    _ = 2 * Real.pi * |inner ℝ ξ v| := by
        rw [inner_smul_right, abs_mul, abs_inv]
        field_simp
end GroundTheory.Automorphic.Sobolev
