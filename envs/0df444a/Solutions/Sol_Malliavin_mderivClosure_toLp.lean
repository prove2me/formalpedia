-- Prove2me | solution 1 for Malliavin.mderivClosure_toLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:05:10.962468+00:00
-- url     : https://prove2.me/submissions/7d72b3a4-1f4a-4c46-88c7-84c533b9610f

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution {F : W → ℝ} (hF : IsSmoothBounded F) :
    mderivClosure μ (hF.toLp μ) = hF.mderivLp μ :=
  mderivClosure_eq μ (hF.inGraphClosure μ)
end Malliavin
