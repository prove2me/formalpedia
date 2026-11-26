-- Prove2me | solution 1 for Malliavin.D12.coe_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:56.248619+00:00
-- url     : https://prove2.me/submissions/418cef3d-6d32-415e-aa48-f75f7f8c7baf

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
namespace D12
theorem _root_.solution (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 μ) :
    (D12.comp μ hφ hK F : Lp ℝ 2 μ) = (memLp_comp_of_deriv_le μ hφ hK F).toLp _ := rfl
end D12
end Malliavin
