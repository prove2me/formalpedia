-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_comp_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:47.909817+00:00
-- url     : https://prove2.me/submissions/0c5efd0e-7aad-4310-8761-c63f9d1cc83c

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_mderivClosure_comp_space
import Theorems.Thm_Malliavin_timeDerivative_smulLp
import Theorems.Thm_Malliavin_wienerIntegral_mem_space


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
    (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_comp_of_deriv_le P hφ hK (wienerIntegral hB g)).toLp _)) =
      tensor g ((memLp_deriv_comp hφ hK (wienerIntegral hB g)).toLp _) := by
  have hmem := wienerIntegral_mem_space hB L hL hgen g
  rw [mderivClosure_comp_space hφ hK ⟨_, hmem⟩, timeDerivative_smulLp hB L hL hgen]
  congr 1
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl
end Malliavin
