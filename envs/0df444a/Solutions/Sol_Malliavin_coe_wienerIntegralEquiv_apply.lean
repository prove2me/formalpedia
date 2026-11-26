-- Prove2me | solution 1 for Malliavin.coe_wienerIntegralEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:38.311868+00:00
-- url     : https://prove2.me/submissions/8ddcc7e9-5a9e-4179-b30e-2bb84fa8069d

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (wienerIntegralEquiv hB f : RandomL2 P) = wienerIntegral hB f := rfl
end Malliavin
