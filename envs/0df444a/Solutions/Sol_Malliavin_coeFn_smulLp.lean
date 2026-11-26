-- Prove2me | solution 1 for Malliavin.coeFn_smulLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:51:04.215013+00:00
-- url     : https://prove2.me/submissions/51971347-fe10-402b-8821-65222bfb86d0

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
theorem _root_.solution (e : E) (G : Lp ℝ 2 μ) :
    (smulLp e G : Ω → E) =ᵐ[μ] fun ω ↦ G ω • e := by
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ e).coeFn_compLpL (p := 2) (μ := μ) G]
    with ω hω
  rw [smulLp, hω, ContinuousLinearMap.toSpanSingleton_apply]
end Malliavin
