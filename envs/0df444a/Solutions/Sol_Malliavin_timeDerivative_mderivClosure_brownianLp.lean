-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_brownianLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:06:13.216156+00:00
-- url     : https://prove2.me/submissions/ff96c541-6e38-4835-a97a-d70800fcdddc

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
import Theorems.Thm_Malliavin_dualLp_mem_domD12
import Theorems.Thm_Malliavin_constOfDual_eq_smulLp
import Theorems.Thm_Malliavin_brownianLp_eq_dualLp
import Theorems.Thm_Malliavin_timeDerivative_smulLp
import Theorems.Thm_Malliavin_wienerIntegralEquiv_symm_ofDual


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
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P (brownianLp hB T)) =
      tensor (intervalIndicator T) (Lp.const 2 P (1 : ℝ)) := by
  rw [brownianLp_eq_dualLp hB L hL T, (dualLp_mem_domD12 P (L T)).2, constOfDual_eq_smulLp,
    timeDerivative_smulLp hB L hL hgen, wienerIntegralEquiv_symm_ofDual hB L hL hgen]
end Malliavin
