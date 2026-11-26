-- Prove2me | solution 1 for Malliavin.integral_wienerIntegralKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:46.930404+00:00
-- url     : https://prove2.me/submissions/8a3ff5b5-1750-4e3c-8320-7412d891d264

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_integral_wienerIntegral

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (f : IteratedKernel 1) :
    ∫ ω, wienerIntegralKernel hB f ω ∂P = 0 :=
  integral_wienerIntegral hB _
end Malliavin
