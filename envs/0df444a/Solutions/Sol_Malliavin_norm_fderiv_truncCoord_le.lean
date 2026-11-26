-- Prove2me | solution 1 for Malliavin.norm_fderiv_truncCoord_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:00.64683+00:00
-- url     : https://prove2.me/submissions/9d94fb94-df05-4365-b8c1-5d30d8e2af91

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_abs_deriv_cutoff_le
import Theorems.Thm_Malliavin_cutoff_contDiff


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
namespace Malliavin
theorem _root_.solution (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖fderiv ℝ (truncCoord m L) x‖ ≤ ∑ i, ‖L i‖ := by
  have hd : ∀ i, DifferentiableAt ℝ (fun x ↦ cutoff m (L i x)) x := fun i ↦
    ((cutoff_contDiff m).differentiable one_ne_zero (L i x)).comp x (L i).differentiableAt
  change ‖fderiv ℝ (fun x (i : Fin n) ↦ cutoff m (L i x)) x‖ ≤ _
  rw [fderiv_pi hd]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [ContinuousLinearMap.pi_apply]
  have hcomp : (fun x ↦ cutoff m (L i x)) = cutoff m ∘ L i := rfl
  rw [hcomp, fderiv_comp x ((cutoff_contDiff m).differentiable one_ne_zero _)
    (L i).differentiableAt, (L i).fderiv, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
    norm_smul, Real.norm_eq_abs]
  calc |L i v| * ‖deriv (cutoff m) (L i x)‖
      ≤ ‖L i‖ * ‖v‖ * 1 := by
        gcongr
        · exact (L i).le_opNorm v
        · rw [Real.norm_eq_abs]
          exact abs_deriv_cutoff_le m _
    _ ≤ (∑ i, ‖L i‖) * ‖v‖ := by
        rw [mul_one]
        gcongr
        exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (L j)) (Finset.mem_univ i)
end Malliavin
