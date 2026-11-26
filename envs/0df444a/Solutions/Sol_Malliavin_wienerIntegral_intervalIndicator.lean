-- Prove2me | solution 1 for Malliavin.wienerIntegral_intervalIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:04.825993+00:00
-- url     : https://prove2.me/submissions/5f77c54a-eb19-4c3c-8071-55038716192b

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_stepToLp_single
import Theorems.Thm_Malliavin_stepToRandom_single

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    wienerIntegral hB (intervalIndicator t) = brownianLp hB t := by
  have := wienerIntegral_stepToLp hB (Finsupp.single t 1)
  rwa [stepToLp_single, stepToRandom_single, one_smul, one_smul] at this
end Malliavin
