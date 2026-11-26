-- Prove2me | solution 1 for Malliavin.coeFn_incrementProductLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:45.107579+00:00
-- url     : https://prove2.me/submissions/28232f36-83a6-4b29-83b4-daf7073a69fd

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
theorem _root_.solution (hB : IsPreBrownianReal B P) (a b c d : ℝ≥0) :
    (incrementProductLp hB a b c d : Ω → ℝ) =ᵐ[P] fun ω ↦ (B b ω - B a ω) * (B d ω - B c ω) :=
  MemLp.coeFn_toLp _
end Malliavin
