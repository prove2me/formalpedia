-- Prove2me | solution 1 for Malliavin.tensorL_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:39.093799+00:00
-- url     : https://prove2.me/submissions/67d95273-e278-45c4-b71f-997c4c2bc6b6

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
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Malliavin
theorem _root_.solution [SFinite μ] [SFinite ν] (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    tensorL g G = tensor g G := rfl
end Malliavin
