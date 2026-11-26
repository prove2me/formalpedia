-- Prove2me | solution 1 for Malliavin.constOfDual_eq_constLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:13.668926+00:00
-- url     : https://prove2.me/submissions/6d8cea43-d25a-44f8-9170-a985ebec4cd6

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
import Theorems.Thm_Malliavin_constLp_apply

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
omit [CompleteSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution (L : StrongDual ℝ W) : constOfDual μ L = constLp μ (ofDual μ L) := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_const (ofDual μ L)), Lp.coeFn_const 2 μ (ofDual μ L)]
    with x h1 h2
  rw [constOfDual, h1, constLp_apply, h2]
  rfl
end Malliavin
