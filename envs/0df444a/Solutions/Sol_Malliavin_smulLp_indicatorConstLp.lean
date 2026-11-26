-- Prove2me | solution 1 for Malliavin.smulLp_indicatorConstLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:55.334622+00:00
-- url     : https://prove2.me/submissions/84fc72e3-95c2-4de4-a23b-0ab23dcf2124

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_FubiniLift
import Theorems.Thm_Malliavin_coeFn_smulLp

set_option autoImplicit false
open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3
open Malliavin
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Malliavin
theorem _root_.solution (e : E) {A : Set Ω} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (c : ℝ) :
    smulLp e (indicatorConstLp 2 hA hμA c) = indicatorConstLp 2 hA hμA (c • e) := by
  apply Lp.ext
  filter_upwards [coeFn_smulLp e (indicatorConstLp 2 hA hμA c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := c • e)] with ω h1 h2 h3
  rw [h1, h2, h3]
  by_cases hω : ω ∈ A <;> simp [hω]
end Malliavin
