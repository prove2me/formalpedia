-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_comp_brownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:11.88619+00:00
-- url     : https://prove2.me/submissions/99bee78e-92d1-4e4a-819e-c8ee86661c56

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_cylinder_expGrowth
import Theorems.Thm_Malliavin_cylinderPartialExp_oneCoord

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
theorem _root_.solution (hgen : IsWienerGenerated B)
    (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|)) (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|))
    (T : ℝ≥0) (hd : MemLp (fun w ↦ deriv g (B T w)) 2 P) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_comp_brownian L hL hg hC hc hgb T).toLp _)) =
      tensor (intervalIndicator T) (hd.toLp _) := by
  have h := timeDerivative_mderivClosure_cylinder_expGrowth hB L hL hgen (contDiff_oneCoord hg)
    hC hc (abs_oneCoord_le hC hc hgb) (norm_fderiv_oneCoord_le hg hC hc hgb') (fun _ ↦ T)
  rw [Fin.sum_univ_one, cylinderPartialExp_oneCoord L hL hg hC hc hgb' T hd] at h
  exact h
end Malliavin
