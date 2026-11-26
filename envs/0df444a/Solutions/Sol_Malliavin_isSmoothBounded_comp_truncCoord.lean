-- Prove2me | solution 1 for Malliavin.isSmoothBounded_comp_truncCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:51.518837+00:00
-- url     : https://prove2.me/submissions/430b3731-739b-4d35-8cd1-821e38f9a209

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_contDiff_truncCoord
import Theorems.Thm_Malliavin_norm_truncCoord_le
import Theorems.Thm_Malliavin_norm_fderiv_truncCoord_le

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (m : ℕ) (L : Fin n → StrongDual ℝ W) :
    IsSmoothBounded (fun x ↦ f (truncCoord m L x)) where
  contDiff := hf.comp (contDiff_truncCoord m L)
  bounded := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin n → ℝ) ((m + 1) * (Real.pi / 2)))
      |>.exists_bound_of_continuousOn hf.continuous.continuousOn
    exact ⟨C, fun x ↦ by
      rw [← Real.norm_eq_abs]
      exact hC _ (mem_closedBall_zero_iff.mpr (norm_truncCoord_le m L x))⟩
  bounded_fderiv := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin n → ℝ) ((m + 1) * (Real.pi / 2)))
      |>.exists_bound_of_continuousOn (hf.continuous_fderiv one_ne_zero).continuousOn
    refine ⟨C * ∑ i, ‖L i‖, fun x ↦ ?_⟩
    have hcomp : (fun x ↦ f (truncCoord m L x)) = f ∘ truncCoord m L := rfl
    rw [hcomp, fderiv_comp x (hf.differentiable one_ne_zero _)
      ((contDiff_truncCoord m L).differentiable one_ne_zero _)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul (hC _ (mem_closedBall_zero_iff.mpr (norm_truncCoord_le m L x)))
      (norm_fderiv_truncCoord_le m L x) (norm_nonneg _)
      ((norm_nonneg _).trans (hC _ (mem_closedBall_zero_iff.mpr (norm_truncCoord_le m L x))))
end Malliavin
