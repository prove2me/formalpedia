-- Prove2me | solution 1 for Malliavin.inner_fubiniLift_tensorLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:51.64584+00:00
-- url     : https://prove2.me/submissions/e3073518-b165-4940-8414-0b01488bb197

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
theorem _root_.solution (U : Lp (Lp ℝ 2 ν) 2 μ) (A : FiniteMeasurableSet μ)
    (g : Lp ℝ 2 ν) :
    ⟪fubiniLift U, tensorLp A g⟫_ℝ = ∫ ω in A.1, ⟪g, U ω⟫_ℝ ∂μ := by
  rw [← fubiniLift_indicatorLp, LinearIsometry.inner_map_map, real_inner_comm, indicatorLp,
    L2.inner_indicatorConstLp_eq_setIntegral_inner ℝ U A.2.1 g A.2.2]
end Malliavin
