-- Prove2me | solution 1 for Malliavin.dense_mderivPMap_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:16.614389+00:00
-- url     : https://prove2.me/submissions/7f953d3a-4b53-449c-bff1-e3489ad9ed7b

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
import Theorems.Thm_Malliavin_dense_domD12

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
theorem _root_.solution :
    Dense ((mderivPMap μ).domain : Set (Lp ℝ 2 μ)) := by
  change Dense (domD12 μ)
  exact dense_domD12 μ
end Malliavin
