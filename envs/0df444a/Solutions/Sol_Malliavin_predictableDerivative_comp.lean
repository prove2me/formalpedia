-- Prove2me | solution 1 for Malliavin.predictableDerivative_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:36:40.719838+00:00
-- url     : https://prove2.me/submissions/6c5f7c35-3526-4eee-a361-f9b119b4b875

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_ClarkOconeFamily_timeDerivative_apply
import Theorems.Thm_Malliavin_D12_coe_comp
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_comp


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
    predictableDerivative C (D12.comp P hφ hK F) =
      predictableProjection 𝓕 (boundedSMul
        (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
          (hφ.continuous_deriv_one.comp_aestronglyMeasurable
            (Lp.aestronglyMeasurable (F : Lp ℝ 2 P))))
        (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK ((F : Lp ℝ 2 P) p.2))
        (C.timeDerivative (mderivD12 P F))) := by
  unfold predictableDerivative
  rw [mderivD12_apply, ClarkOconeFamily.timeDerivative_apply, D12.coe_comp,
    timeDerivative_mderivClosure_comp C.isPreBrownian C.coordinate C.coordinate_apply C.generated
      hφ hK F.2, ClarkOconeFamily.timeDerivative_apply, mderivD12_apply]
end Malliavin
