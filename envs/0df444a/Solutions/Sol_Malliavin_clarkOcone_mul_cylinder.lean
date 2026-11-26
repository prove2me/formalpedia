-- Prove2me | solution 1 for Malliavin.clarkOcone_mul_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:51:00.21111+00:00
-- url     : https://prove2.me/submissions/0f5bd422-4e0a-429e-81e7-6150b71b7e64

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_ClarkOconeFamily_timeDerivative_apply
import Theorems.Thm_Malliavin_clarkOcone
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_mul_cylinder


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
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K) (hb' : ∃ K', ∀ y, ‖fderiv ℝ f y‖ ≤ K') (t : Fin n → ℝ≥0)
    {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    (memLp_mul_smoothBounded P
        (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) F).toLp _ =
      expectationL2 ((memLp_mul_smoothBounded P
        (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) F).toLp _)
        + C.itoIntegral (predictableProjection 𝓕
          (boundedSMul (G := fun p : ℝ≥0 × W ↦ f (fun i ↦ B (t i) p.2))
            (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
              (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb'
                t).continuous.aestronglyMeasurable)
            (C := K) (fun p ↦ hb (fun i ↦ B (t i) p.2))
            (C.timeDerivative (mderivD12 P ⟨F, hF⟩)) +
          ∑ i, tensor (intervalIndicator (t i))
            ((memLp_mul_cylinderPartial C.coordinate C.coordinate_apply f hf hb' t F i).toLp
              _))) := by
  have hmem := (mul_mem_domD12 P
    (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) hF).1
  have h := clarkOcone C ⟨_, hmem⟩
  rw [clarkOconeIntegral, predictableDerivative, mderivD12_apply,
    ClarkOconeFamily.timeDerivative_apply] at h
  change (memLp_mul_smoothBounded P
      (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) F).toLp _ =
    expectationL2 ((memLp_mul_smoothBounded P
      (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) F).toLp _)
      + C.itoIntegral (predictableProjection 𝓕 (timeDerivative C.isPreBrownian C.coordinate
        C.coordinate_apply C.generated (mderivClosure P ((memLp_mul_smoothBounded P
          (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t)
            F).toLp _)))) at h
  rwa [timeDerivative_mderivClosure_mul_cylinder C.isPreBrownian C.coordinate
    C.coordinate_apply C.generated f hf hb hb' t hF] at h
end Malliavin
