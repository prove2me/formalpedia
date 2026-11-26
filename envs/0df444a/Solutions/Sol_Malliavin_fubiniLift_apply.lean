-- Prove2me | solution 1 for Malliavin.fubiniLift_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:31.454174+00:00
-- url     : https://prove2.me/submissions/e98fd165-a1c5-428d-8c0a-6651e5a6cd2f

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
namespace Malliavin
theorem _root_.solution (f : Lp (Lp ℝ 2 ν) 2 μ) : fubiniLift f = fubiniLiftL f := rfl
end Malliavin
