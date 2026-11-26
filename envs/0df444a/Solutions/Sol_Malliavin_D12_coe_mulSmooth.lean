-- Prove2me | solution 1 for Malliavin.D12.coe_mulSmooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:23.854712+00:00
-- url     : https://prove2.me/submissions/b39cb59e-1b1a-4144-a2da-dcadac87d48b

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
namespace D12
theorem _root_.solution (hG : IsSmoothBounded G) (F : D12 μ) :
    (D12.mulSmooth μ hG F : Lp ℝ 2 μ) = (memLp_mul_smoothBounded μ hG F).toLp _ := rfl
end D12
end Malliavin
