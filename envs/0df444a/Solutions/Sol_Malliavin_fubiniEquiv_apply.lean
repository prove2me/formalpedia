-- Prove2me | solution 1 for Malliavin.fubiniEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:43.52784+00:00
-- url     : https://prove2.me/submissions/8d99e3ae-07ad-47a9-84d6-d4ce2851b66f

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
variable [SFinite μ] [SFinite ν]
variable [SigmaFinite μ] [SigmaFinite ν]
namespace Malliavin
theorem _root_.solution (f : Lp (Lp ℝ 2 ν) 2 μ) : fubiniEquiv f = fubiniLift f := rfl
end Malliavin
