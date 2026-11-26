-- Prove2me | solution 1 for Malliavin.dense_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:49.970845+00:00
-- url     : https://prove2.me/submissions/11cdc1a9-b4cd-44f6-969a-83e94d80c763

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
theorem _root_.solution : Dense (domD12 μ) := by
  apply (denseRange_toLp μ).mono
  rintro _ ⟨F, rfl⟩
  exact F.2.toLp_mem_domD12 μ
end Malliavin
