-- Prove2me | solution 1 for Malliavin.clarkOcone_comp_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:50:53.37373+00:00
-- url     : https://prove2.me/submissions/a5dcd87b-18e3-4f84-8efe-c662a828c777

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_ClarkOconeFamily_timeDerivative_apply
import Theorems.Thm_Malliavin_clarkOcone
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_comp_pi
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



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
    (D12.compPi P hf hK F : Lp ℝ 2 P) =
      expectationL2 (D12.compPi P hf hK F : Lp ℝ 2 P) +
        C.itoIntegral (predictableProjection 𝓕 (∑ i,
          boundedSMul (G := fun p : ℝ≥0 × W ↦ fderiv ℝ f (fun i ↦ (F i : Lp ℝ 2 P) p.2)
              (Pi.single i 1))
            (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
              (memLp_fderiv_pi_comp hf hK (fun i ↦ (F i : Lp ℝ 2 P)) i).aestronglyMeasurable)
            (C := K) (fun _ ↦ abs_fderiv_pi_single_le hK _ i)
            (C.timeDerivative (mderivD12 P (F i))))) := by
  have h := clarkOcone C (D12.compPi P hf hK F)
  rw [clarkOconeIntegral, predictableDerivative, mderivD12_apply,
    ClarkOconeFamily.timeDerivative_apply] at h
  change (D12.compPi P hf hK F : Lp ℝ 2 P) = expectationL2 (D12.compPi P hf hK F : Lp ℝ 2 P) +
    C.itoIntegral (predictableProjection 𝓕 (timeDerivative C.isPreBrownian C.coordinate
      C.coordinate_apply C.generated (mderivClosure P
        ((memLp_comp_pi P hf hK fun i ↦ (F i : Lp ℝ 2 P)).toLp _)))) at h
  rw [timeDerivative_mderivClosure_comp_pi C.isPreBrownian C.coordinate C.coordinate_apply
    C.generated hf hK fun i ↦ (F i).2] at h
  simpa only [ClarkOconeFamily.timeDerivative_apply, mderivD12_apply] using h
end Malliavin
