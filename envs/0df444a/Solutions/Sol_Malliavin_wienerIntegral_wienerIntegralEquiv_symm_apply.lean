-- Prove2me | solution 1 for Malliavin.wienerIntegral_wienerIntegralEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:32.718307+00:00
-- url     : https://prove2.me/submissions/debbc1f9-9537-475f-8d52-df30a0acb6cb

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
import Theorems.Thm_Malliavin_coe_wienerIntegralEquiv_apply

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (Z : firstChaos hB) :
    wienerIntegral hB ((wienerIntegralEquiv hB).symm Z) = (Z : RandomL2 P) := by
  rw [← coe_wienerIntegralEquiv_apply]
  exact congrArg Subtype.val ((wienerIntegralEquiv hB).apply_symm_apply Z)
end Malliavin
