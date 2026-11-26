-- Prove2me | solution 1 for Malliavin.inner_wienerIntegralEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:28:21.304787+00:00
-- url     : https://prove2.me/submissions/89687301-7541-4774-aaf2-18cb2411ad1e

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
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) (Z : firstChaos hB) :
    ⟪g, (wienerIntegralEquiv hB).symm Z⟫_ℝ = ⟪wienerIntegral hB g, (Z : RandomL2 P)⟫_ℝ := by
  rw [← (wienerIntegralEquiv hB).inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  rfl
end Malliavin
