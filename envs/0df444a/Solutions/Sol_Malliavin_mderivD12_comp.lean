-- Prove2me | solution 1 for Malliavin.mderivD12_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:06.35109+00:00
-- url     : https://prove2.me/submissions/d7b568be-5b06-425e-a8a6-14cceb0de36b

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
theorem _root_.solution (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 μ) :
    mderivD12 μ (D12.comp μ hφ hK F) =
      (memLp_deriv_smul_of_deriv_le μ hφ hK F (mderivD12 μ F)).toLp _ :=
  (comp_mem_domD12 μ hφ hK F.2).2
end Malliavin
