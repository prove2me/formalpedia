-- Prove2me | solution 1 for Malliavin.coeFn_stepToRandom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:03.483913+00:00
-- url     : https://prove2.me/submissions/ecaaa805-d186-4fc6-b0a1-c4b168d0b060

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_stepToRandom_single
import Theorems.Thm_Malliavin_stepSum_zero
import Theorems.Thm_Malliavin_stepSum_single_add

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
open CameronMartin
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    (stepToRandom hB v : Ω → ℝ) =ᵐ[P] stepSum B v := by
  induction v using Finsupp.induction with
  | zero =>
    rw [map_zero, stepSum_zero]
    exact Lp.coeFn_zero _ _ _
  | single_add t c v _ _ ih =>
    rw [map_add, stepToRandom_single, stepSum_single_add t c v]
    filter_upwards [Lp.coeFn_add (c • brownianLp hB t) (stepToRandom hB v),
      Lp.coeFn_smul c (brownianLp hB t), coeFn_brownianLp hB t, ih] with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
end Malliavin
