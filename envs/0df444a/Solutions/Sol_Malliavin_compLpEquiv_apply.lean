-- Prove2me | solution 1 for Malliavin.compLpEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:20.678289+00:00
-- url     : https://prove2.me/submissions/07e8e8f5-516c-4c2f-930a-61a1027bfb71

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
namespace Malliavin
theorem _root_.solution (e : E ≃ₗᵢ[ℝ] F) (f : Lp E 2 μ) :
    compLpEquiv e f = compLpₗᵢ e.toLinearIsometry f := rfl
end Malliavin
