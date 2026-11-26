-- Prove2me | solution 1 for Malliavin.coeFn_fubiniLift_indicatorLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:37.235689+00:00
-- url     : https://prove2.me/submissions/5dd6ab01-5cae-43e7-8756-cbf6b40f3089

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
theorem _root_.solution (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    (fubiniLift (indicatorLp A g) : T × Ω → ℝ) =ᵐ[ν.prod μ]
      fun p ↦ g p.1 * A.1.indicator (1 : Ω → ℝ) p.2 := by
  rw [fubiniLift_indicatorLp]
  exact coeFn_tensorLp A g
end Malliavin
