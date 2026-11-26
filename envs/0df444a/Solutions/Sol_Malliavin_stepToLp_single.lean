-- Prove2me | solution 1 for Malliavin.stepToLp_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:16.896085+00:00
-- url     : https://prove2.me/submissions/83bcfaa9-ba01-400d-847a-b1cc2cee069f

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (t : ℝ≥0) (c : ℝ) :
    stepToLp (Finsupp.single t c) = c • intervalIndicator t :=
  Finsupp.linearCombination_single _ _ _
end Malliavin
