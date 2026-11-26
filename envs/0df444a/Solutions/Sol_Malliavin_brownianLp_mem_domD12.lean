-- Prove2me | solution 1 for Malliavin.brownianLp_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:06:08.244513+00:00
-- url     : https://prove2.me/submissions/5655d4c5-4ff2-460d-9273-e9060a847013

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
import Theorems.Thm_Malliavin_dualLp_mem_domD12
import Theorems.Thm_Malliavin_brownianLp_eq_dualLp

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (t : ℝ≥0) : brownianLp hB t ∈ domD12 P := by
  rw [brownianLp_eq_dualLp hB L hL t]
  exact (dualLp_mem_domD12 P (L t)).1
end Malliavin
