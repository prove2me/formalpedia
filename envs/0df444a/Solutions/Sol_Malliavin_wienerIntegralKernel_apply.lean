-- Prove2me | solution 1 for Malliavin.wienerIntegralKernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:52.698524+00:00
-- url     : https://prove2.me/submissions/79204b77-f6e4-4655-9c61-0836f3cbafc5

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
theorem _root_.solution (hB : IsPreBrownianReal B P) (f : IteratedKernel 1) :
    wienerIntegralKernel hB f = wienerIntegral hB (kernelToLine f) := rfl
end Malliavin
