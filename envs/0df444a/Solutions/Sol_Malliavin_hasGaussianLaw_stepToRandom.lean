-- Prove2me | solution 1 for Malliavin.hasGaussianLaw_stepToRandom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:19.867694+00:00
-- url     : https://prove2.me/submissions/2865b066-632a-46c3-8e87-16c2ed378404

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_hasGaussianLaw_stepSum
import Theorems.Thm_Malliavin_coeFn_stepToRandom

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
open CameronMartin
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    HasGaussianLaw (stepToRandom hB v : Ω → ℝ) P :=
  (hasGaussianLaw_stepSum hB v).congr (coeFn_stepToRandom hB v).symm
end Malliavin
