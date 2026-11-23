-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:38:36.560626+00:00
-- url     : https://prove2.me/submissions/75d15767-0592-4068-ac4e-eabba47d8636

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_lintegral_min_one_sq_lt_top
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_triplet_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_jump_split_integrable_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_large_jump_lower
set_option autoImplicit false
open MeasureTheory Filter Set
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) :
    ∀ θ : ℝ, 0 < θ →
      D.triplet.drift + D.gaussianCoefficient ^ 2 * θ / 2 +
          (∫ y in Ioo (-1 : ℝ) 0,
            (Real.exp (θ * y) - 1 - θ * y) / θ ∂D.triplet.levyMeasure) -
          (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂D.triplet.levyMeasure) / θ
        ≤ ψ θ / θ := by
  intro θ hθ
  let μ : Measure ℝ := D.triplet.levyMeasure
  have hlevy : ProbabilityTheory.IsLevyMeasure μ := by
    simpa [μ] using D.triplet.levyMeasure_isLevyMeasure
  have hμ : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ := by
    refine ⟨(continuous_const.min (continuous_pow 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have henorm : ∀ y : ℝ, ‖min 1 (y ^ 2)‖ₑ = ENNReal.ofReal (min 1 (y ^ 2)) := fun y =>
      Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg y))
    simp_rw [henorm]
    exact hlevy.lintegral_min_one_sq_lt_top
  have htrip := Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_triplet_eq
    P D ψ hψ θ hθ
  have hsplit := Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_jump_split_integrable_v2
    μ hμ θ hθ
  have hlarge := Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_large_jump_lower
    μ hμ θ hθ
  have hlarge' :
      -((∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂μ) / θ) ≤
        ∫ y in Iic (-1 : ℝ), (Real.exp (θ * y) - 1) / θ ∂μ := by
    simpa only [neg_div] using hlarge
  dsimp [μ] at hsplit hlarge' ⊢
  linarith
