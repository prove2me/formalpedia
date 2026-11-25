-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_derivSymb_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:00.746306+00:00
-- url     : https://prove2.me/submissions/2f981b6e-51f7-46cc-ac67-3250644e52a6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
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
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {k : ℕ} (w : Fin k → E) (ξ : E) :
    ‖derivSymb w ξ‖ ≤ (∏ j, (2 * Real.pi * ‖w j‖)) * ‖ξ‖ ^ k := by
  rw [derivSymb, norm_prod, ← Fin.prod_const k ‖ξ‖, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun j _ ↦ norm_nonneg _) fun j _ ↦ ?_
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos, h2]
  calc 2 * Real.pi * |inner ℝ ξ (w j)| ≤ 2 * Real.pi * (‖ξ‖ * ‖w j‖) := by
        gcongr; exact abs_real_inner_le_norm ξ (w j)
    _ = _ := by ring
end GroundTheory.Automorphic.Sobolev
