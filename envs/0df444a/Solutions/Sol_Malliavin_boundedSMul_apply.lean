-- Prove2me | solution 1 for Malliavin.boundedSMul_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:44.050664+00:00
-- url     : https://prove2.me/submissions/7a4bf1f8-d034-4645-809f-a7456a9e2173

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_FubiniLift

set_option autoImplicit false
open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3
open Malliavin
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E]
namespace Malliavin
theorem _root_.solution {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) :
    boundedSMul hG hC U = (memLp_boundedSMul hG hC U).toLp _ := rfl
end Malliavin
