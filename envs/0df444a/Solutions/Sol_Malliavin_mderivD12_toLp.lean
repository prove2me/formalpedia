-- Prove2me | solution 1 for Malliavin.mderivD12_toLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:12.229675+00:00
-- url     : https://prove2.me/submissions/9508967e-fe8b-4845-8068-c8a14810c982

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
import Theorems.Thm_Malliavin_mderivClosure_toLp

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
    mderivD12 μ ⟨hF.toLp μ, hF.toLp_mem_domD12 μ⟩ = hF.mderivLp μ :=
  mderivClosure_toLp μ hF
end Malliavin
