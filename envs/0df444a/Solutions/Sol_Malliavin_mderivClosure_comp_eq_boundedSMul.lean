-- Prove2me | solution 1 for Malliavin.mderivClosure_comp_eq_boundedSMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:20.70022+00:00
-- url     : https://prove2.me/submissions/a0182478-c659-4667-b462-e40493548dc4

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_coeFn_boundedSMul


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  {φ : ℝ → ℝ} {K : ℝ≥0}
namespace Malliavin
theorem _root_.solution (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    mderivClosure P ((memLp_comp_of_deriv_le P hφ hK F).toLp _) =
      boundedSMul (hφ.continuous_deriv_one.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F))
        (C := K) (fun x ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK (F x))
        (mderivClosure P F) := by
  rw [(comp_mem_domD12 P hφ hK hF).2]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_deriv_smul_of_deriv_le P hφ hK F (mderivClosure P F)),
    coeFn_boundedSMul (hφ.continuous_deriv_one.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable F)) (C := K) (fun x ↦ by
        rw [← Real.norm_eq_abs]; exact_mod_cast hK (F x)) (mderivClosure P F)] with x h1 h2
  rw [h1, h2]
end Malliavin
