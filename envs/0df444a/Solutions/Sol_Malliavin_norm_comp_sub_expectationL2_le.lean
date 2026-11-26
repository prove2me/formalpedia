-- Prove2me | solution 1 for Malliavin.norm_comp_sub_expectationL2_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:51:42.509216+00:00
-- url     : https://prove2.me/submissions/5c7e41c3-3fcc-4870-9fc3-b9641652805a

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_norm_mderivClosure_comp_le
import Theorems.Thm_Malliavin_norm_sub_expectationL2_le_mderivD12


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 P) :
    ‖(D12.comp P hφ hK F : Lp ℝ 2 P) - expectationL2 (D12.comp P hφ hK F : Lp ℝ 2 P)‖ ≤
      K * ‖mderivD12 P F‖ :=
  (norm_sub_expectationL2_le_mderivD12 C (D12.comp P hφ hK F)).trans
    (norm_mderivClosure_comp_le P hφ hK F.2)
end Malliavin
