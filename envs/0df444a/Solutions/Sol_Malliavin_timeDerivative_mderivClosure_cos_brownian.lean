-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_cos_brownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:06:28.931825+00:00
-- url     : https://prove2.me/submissions/270f00d0-fb7f-441e-9afd-3b6882346d26

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_abs_cos_le_exp_abs
import Theorems.Thm_Malliavin_abs_deriv_cos_le_exp_abs
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_comp_brownian

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL
variable {g : ℝ → ℝ}
namespace Malliavin
theorem _root_.solution (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_cos_brownian L hL T).toLp _)) =
      tensor (intervalIndicator T) (-(memLp_sin_brownian L hL T).toLp _) := by
  have hd : MemLp (fun w ↦ deriv Real.cos (B T w)) 2 P := by
    have h := (memLp_sin_brownian (P := P) L hL T).neg
    refine MemLp.ae_eq (Filter.Eventually.of_forall fun w ↦ ?_) h
    change -Real.sin (B T w) = deriv Real.cos (B T w)
    rw [Real.deriv_cos]
  have h := timeDerivative_mderivClosure_comp_brownian hB L hL hgen Real.contDiff_cos
    zero_le_one zero_le_one abs_cos_le_exp_abs abs_deriv_cos_le_exp_abs T hd
  rw [h]
  congr 1
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp hd, Lp.coeFn_neg ((memLp_sin_brownian L hL T).toLp _),
    MemLp.coeFn_toLp (memLp_sin_brownian L hL T)] with w h1 h2 h3
  rw [h1, h2, Pi.neg_apply, h3, Real.deriv_cos]
end Malliavin
