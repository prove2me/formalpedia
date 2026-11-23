-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_superlinear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:51:20.995474+00:00
-- url     : https://prove2.me/submissions/a93d0749-f803-42e7-b7fe-84ba80ccebb2

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_lintegral_min_one_sq_lt_top
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_norm_lower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_gaussian_growth
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_jump_growth
set_option autoImplicit false
open MeasureTheory Filter Set
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hnbv : ¬ HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧ ∀ θ : ℝ, β ≤ θ → C < ψ θ / θ := by
  intro C
  let μ : Measure ℝ := D.triplet.levyMeasure
  let B : ℝ := ∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂μ
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg (fun _ => zero_le_one)
  have hμ : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ := by
    refine ⟨(continuous_const.min (continuous_pow 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have henorm : ∀ y : ℝ, ‖min 1 (y ^ 2)‖ₑ = ENNReal.ofReal (min 1 (y ^ 2)) := fun y =>
      Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg y))
    simp_rw [henorm]
    exact (by simpa [μ] using D.triplet.levyMeasure_isLevyMeasure :
      ProbabilityTheory.IsLevyMeasure μ).lintegral_min_one_sq_lt_top
  rcases lt_or_eq_of_le D.gaussianNonnegative with hσpos | hσzero
  · let a : ℝ := D.gaussianCoefficient ^ 2 / 2
    have ha : 0 < a := by dsimp [a]; positivity
    rcases Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_gaussian_growth
        μ D.triplet.drift a B ha hB C with ⟨β, hβone, hβ⟩
    refine ⟨β, hβone, ?_⟩
    intro θ hθβ
    have hθpos : 0 < θ := lt_of_lt_of_le zero_lt_one (hβone.trans hθβ)
    have hg := hβ θ hθβ
    have hlow := Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_norm_lower
      P D ψ hψ θ hθpos
    dsimp [a, μ, B] at hg hlow ⊢
    linarith
  · have hinf : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂μ) = ⊤ := by
      by_contra hnot
      apply hnbv
      exact ⟨hσzero.symm, lt_top_iff_ne_top.mpr (by simpa [μ] using hnot)⟩
    rcases Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_jump_growth
        μ hμ hinf (C - D.triplet.drift + B + 1) with ⟨β, hβone, hβ⟩
    refine ⟨β, hβone, ?_⟩
    intro θ hθβ
    have hθpos : 0 < θ := lt_of_lt_of_le zero_lt_one (hβone.trans hθβ)
    have hmass_real :
        D.triplet.levyMeasure.real (Iic (-1 : ℝ)) = B := by
      simpa [B, μ] using
        (setIntegral_const (μ := D.triplet.levyMeasure) (s := Iic (-1 : ℝ)) (1 : ℝ)).symm
    have hBdiv : B / θ ≤ B := by
      apply (div_le_iff₀ hθpos).2
      simpa using mul_le_mul_of_nonneg_left (hβone.trans hθβ) hB
    have hj := hβ θ hθβ
    have hlow := Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_norm_lower
      P D ψ hψ θ hθpos
    dsimp [B, μ] at hj hBdiv hlow ⊢
    rw [← hσzero] at hlow
    norm_num at hlow
    rw [hmass_real] at hlow
    linarith
