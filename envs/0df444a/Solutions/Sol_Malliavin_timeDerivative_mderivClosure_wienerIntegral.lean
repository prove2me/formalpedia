-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:49.467128+00:00
-- url     : https://prove2.me/submissions/6cdf3edb-5b66-4e20-90a3-4fdf1c00348c

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
import Theorems.Thm_Malliavin_coe_space_mem_domD12
import Theorems.Thm_Malliavin_constLp_eq_smulLp
import Theorems.Thm_Malliavin_wienerIntegral_mem_space
import Theorems.Thm_Malliavin_timeDerivative_smulLp


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
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivative hB L hL hgen (mderivClosure P (wienerIntegral hB g)) =
      tensor g (Lp.const 2 P (1 : ℝ)) := by
  have hmem := wienerIntegral_mem_space hB L hL hgen g
  rw [(coe_space_mem_domD12 P ⟨_, hmem⟩).2, constLp_eq_smulLp, timeDerivative_smulLp hB L hL hgen]
  congr 1
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl
end Malliavin
