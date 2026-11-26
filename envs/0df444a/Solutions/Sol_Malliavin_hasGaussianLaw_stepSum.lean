-- Prove2me | solution 1 for Malliavin.hasGaussianLaw_stepSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:08.173747+00:00
-- url     : https://prove2.me/submissions/b16d13c9-ded8-4d9f-a757-eb428e165212

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_isGaussianProcess_stepSum

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
open CameronMartin
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    HasGaussianLaw (stepSum B v) P :=
  (isGaussianProcess_stepSum hB).hasGaussianLaw_eval v
end Malliavin
