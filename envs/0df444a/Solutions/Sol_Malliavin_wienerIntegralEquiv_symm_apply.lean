-- Prove2me | solution 1 for Malliavin.wienerIntegralEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:21.253188+00:00
-- url     : https://prove2.me/submissions/112d7222-8d4c-43dc-b10c-1993dc840b0c

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
import Theorems.Thm_Malliavin_range_wienerIntegral


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (wienerIntegralEquiv hB).symm ⟨wienerIntegral hB f, by
      rw [← range_wienerIntegral]; exact ⟨f, rfl⟩⟩ = f := by
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl
end Malliavin
