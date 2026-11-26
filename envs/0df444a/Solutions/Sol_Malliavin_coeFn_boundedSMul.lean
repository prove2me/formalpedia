-- Prove2me | solution 1 for Malliavin.coeFn_boundedSMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:53:59.773313+00:00
-- url     : https://prove2.me/submissions/1b97d739-1cc3-44b3-a0ad-ea5646d5e595

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
    (boundedSMul hG hC U : Ω → E) =ᵐ[μ] fun x ↦ G x • U x :=
  MemLp.coeFn_toLp (memLp_boundedSMul hG hC U)
end Malliavin
