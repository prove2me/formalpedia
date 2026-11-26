-- Prove2me | solution 1 for Malliavin.inner_timeDerivativeOfFirstChaos_tensorLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:52.122737+00:00
-- url     : https://prove2.me/submissions/accfbcdb-7216-47a0-93b2-9addafb2981e

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
import Theorems.Thm_Malliavin_inner_wienerIntegralEquiv_symm
import Theorems.Thm_Malliavin_timeDerivativeOfFirstChaos_apply
import Theorems.Thm_Malliavin_inner_fubiniLift_tensorLp


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} [SFinite P]
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (U : Lp (firstChaos hB) 2 P) (A : FiniteMeasurableSet P)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪timeDerivativeOfFirstChaos hB U, tensorLp A g⟫_ℝ =
      ∫ ω in A.1, ⟪wienerIntegral hB g, (U ω : RandomL2 P)⟫_ℝ ∂P := by
  rw [timeDerivativeOfFirstChaos_apply, inner_fubiniLift_tensorLp]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (coeFn_compLpₗᵢ (wienerIntegralEquiv hB).symm.toLinearIsometry U)] with ω hω
  rw [hω, LinearIsometryEquiv.coe_toLinearIsometry, inner_wienerIntegralEquiv_symm]
end Malliavin
