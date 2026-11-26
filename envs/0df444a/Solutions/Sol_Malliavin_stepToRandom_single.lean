-- Prove2me | solution 1 for Malliavin.stepToRandom_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:51:57.263287+00:00
-- url     : https://prove2.me/submissions/4a38f3bc-7b26-4196-8e39-155df44985aa

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
theorem _root_.solution (hB : IsPreBrownianReal B P) (t : ℝ≥0) (c : ℝ) :
    stepToRandom hB (Finsupp.single t c) = c • brownianLp hB t :=
  Finsupp.linearCombination_single _ _ _
end Malliavin
