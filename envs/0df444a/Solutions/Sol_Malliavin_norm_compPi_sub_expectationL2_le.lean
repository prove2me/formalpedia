-- Prove2me | solution 1 for Malliavin.norm_compPi_sub_expectationL2_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:51.147365+00:00
-- url     : https://prove2.me/submissions/e176dfc3-5e63-4082-9bee-46c736b9c578

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_norm_mderivClosure_comp_pi_le
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
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (F : Fin n → D12 P) :
    ‖(D12.compPi P hf hK F : Lp ℝ 2 P) - expectationL2 (D12.compPi P hf hK F : Lp ℝ 2 P)‖ ≤
      K * ∑ i, ‖mderivD12 P (F i)‖ :=
  (norm_sub_expectationL2_le_mderivD12 C (D12.compPi P hf hK F)).trans
    (norm_mderivClosure_comp_pi_le P hf hK fun i ↦ (F i).2)
end Malliavin
