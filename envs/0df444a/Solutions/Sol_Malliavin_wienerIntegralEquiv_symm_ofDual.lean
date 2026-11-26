-- Prove2me | solution 1 for Malliavin.wienerIntegralEquiv_symm_ofDual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:32.190677+00:00
-- url     : https://prove2.me/submissions/c44d942a-6cde-4fff-afd7-683de0a9d424

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
import Theorems.Thm_Malliavin_coe_wienerIntegralEquiv_apply
import Theorems.Thm_Malliavin_wienerIntegral_intervalIndicator


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (t : ℝ≥0) :
    (wienerIntegralEquiv hB).symm
        (LinearIsometryEquiv.ofEq _ _ (space_eq_firstChaos hB L hL hgen) (ofDual P (L t))) =
      intervalIndicator t := by
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [LinearIsometryEquiv.coe_ofEq_apply, coe_wienerIntegralEquiv_apply,
    wienerIntegral_intervalIndicator, brownianLp_eq_ofDual hB L hL t]
end Malliavin
