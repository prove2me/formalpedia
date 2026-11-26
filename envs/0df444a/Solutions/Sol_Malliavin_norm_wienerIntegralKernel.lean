-- Prove2me | solution 1 for Malliavin.norm_wienerIntegralKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:49.910429+00:00
-- url     : https://prove2.me/submissions/d437cf8a-a772-46a6-bd0b-f234b97b839e

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_wienerIntegralKernel_apply

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (f : IteratedKernel 1) :
    ‖wienerIntegralKernel hB f‖ = ‖f‖ := by
  rw [wienerIntegralKernel_apply, norm_wienerIntegral, LinearIsometry.norm_map]
end Malliavin
