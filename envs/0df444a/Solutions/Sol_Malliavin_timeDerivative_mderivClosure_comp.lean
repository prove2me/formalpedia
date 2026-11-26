-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:49.811457+00:00
-- url     : https://prove2.me/submissions/726a2324-dd06-4ed7-beae-76f73ff22149

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_mderivClosure_comp_eq_boundedSMul
import Theorems.Thm_Malliavin_timeDerivative_boundedSMul


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  {φ : ℝ → ℝ} {K : ℝ≥0}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_comp_of_deriv_le P hφ hK F).toLp _)) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
          (hφ.continuous_deriv_one.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)))
        (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK (F p.2))
        (timeDerivative hB L hL hgen (mderivClosure P F)) := by
  rw [mderivClosure_comp_eq_boundedSMul hφ hK hF, timeDerivative_boundedSMul hB L hL hgen]
end Malliavin
