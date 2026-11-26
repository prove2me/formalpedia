-- Prove2me | solution 1 for Malliavin.norm_comp_sub_expectationL2_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:50:33.653228+00:00
-- url     : https://prove2.me/submissions/569dfbd8-70da-43d4-97fd-9167f1162f5d

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_predictableDerivative_comp
import Theorems.Thm_Malliavin_norm_sub_expectationL2


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
    ‖(D12.comp P hφ hK F : Lp ℝ 2 P) - expectationL2 (D12.comp P hφ hK F : Lp ℝ 2 P)‖ =
      ‖predictableProjection 𝓕 (boundedSMul
        (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
          (hφ.continuous_deriv_one.comp_aestronglyMeasurable
            (Lp.aestronglyMeasurable (F : Lp ℝ 2 P))))
        (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK ((F : Lp ℝ 2 P) p.2))
        (C.timeDerivative (mderivD12 P F)))‖ := by
  rw [norm_sub_expectationL2 C, predictableDerivative_comp]
end Malliavin
