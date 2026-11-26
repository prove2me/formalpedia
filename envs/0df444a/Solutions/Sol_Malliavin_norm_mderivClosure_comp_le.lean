-- Prove2me | solution 1 for Malliavin.norm_mderivClosure_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:53.901244+00:00
-- url     : https://prove2.me/submissions/2da7bb4d-660f-401c-8eb4-31e1c4961317

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
variable {φ : ℝ → ℝ} {K : ℝ≥0}
namespace Malliavin
theorem _root_.solution (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    ‖mderivClosure μ ((memLp_comp_of_deriv_le μ hφ hK F).toLp _)‖ ≤ K * ‖mderivClosure μ F‖ := by
  rw [(comp_mem_domD12 μ hφ hK hF).2]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_deriv_smul_of_deriv_le μ hφ hK F (mderivClosure μ F))]
    with x hx
  rw [hx, norm_smul]
  have h1 : ‖deriv φ (F x)‖ ≤ K := by exact_mod_cast hK (F x)
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
end Malliavin
