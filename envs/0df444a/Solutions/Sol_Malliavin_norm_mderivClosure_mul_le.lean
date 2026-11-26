-- Prove2me | solution 1 for Malliavin.norm_mderivClosure_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:16.567799+00:00
-- url     : https://prove2.me/submissions/f9161619-cd4c-416f-8a55-04ab0448cf72

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
variable {G : W → ℝ}
namespace Malliavin
theorem _root_.solution (hG : IsSmoothBounded G) {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ)
    {D D' : ℝ} (hD : ∀ x, |G x| ≤ D) (hD' : ∀ x, ‖mderiv μ G x‖ ≤ D') :
    ‖mderivClosure μ ((memLp_mul_smoothBounded μ hG F).toLp _)‖ ≤
      D' * ‖F‖ + D * ‖mderivClosure μ F‖ := by
  rw [(mul_mem_domD12 μ hG hF).2]
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hD'0 : 0 ≤ D' := (norm_nonneg _).trans (hD' 0)
  have h1 : MemLp (fun x ↦ G x • (mderivClosure μ F) x) 2 μ := by
    have hg : MemLp (fun x ↦ D * ‖(mderivClosure μ F) x‖) 2 μ :=
      (Lp.memLp (mderivClosure μ F)).norm.const_mul _
    refine MemLp.of_le hg (hG.continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable _)) (Filter.Eventually.of_forall fun x ↦ ?_)
    have h0 : 0 ≤ D * ‖(mderivClosure μ F) x‖ := mul_nonneg hD0 (norm_nonneg _)
    rw [Real.norm_eq_abs (D * _), abs_of_nonneg h0, norm_smul]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hD x) (norm_nonneg _)
  have h2 : MemLp (fun x ↦ F x • mderiv μ G x) 2 μ := by
    have hg : MemLp (fun x ↦ D' * ‖F x‖) 2 μ := (Lp.memLp F).norm.const_mul _
    refine MemLp.of_le hg ((Lp.aestronglyMeasurable F).smul
      hG.continuous_mderiv.aestronglyMeasurable) (Filter.Eventually.of_forall fun x ↦ ?_)
    have h0 : 0 ≤ D' * ‖F x‖ := mul_nonneg hD'0 (norm_nonneg _)
    rw [Real.norm_eq_abs (D' * _), abs_of_nonneg h0, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hD' x) (norm_nonneg _)
  have hsplit : (memLp_mul_deriv μ hG F (mderivClosure μ F)).toLp _ =
      h1.toLp _ + h2.toLp _ := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x ↦ rfl)
  rw [hsplit]
  refine (norm_add_le (h1.toLp _) (h2.toLp _)).trans ?_
  rw [add_comm (D' * ‖F‖)]
  refine add_le_add ?_ ?_
  · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [MemLp.coeFn_toLp h1] with x hx
    rw [hx, norm_smul]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hD x) (norm_nonneg _)
  · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [MemLp.coeFn_toLp h2] with x hx
    rw [hx, norm_smul, mul_comm ‖F x‖]
    exact mul_le_mul_of_nonneg_right (hD' x) (norm_nonneg _)
end Malliavin
