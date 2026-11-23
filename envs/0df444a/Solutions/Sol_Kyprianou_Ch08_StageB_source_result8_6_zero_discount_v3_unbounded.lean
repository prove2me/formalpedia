-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:50:54.158482+00:00
-- url     : https://prove2.me/submissions/0808dab9-c159-4d56-9c90-cc7a9133fbdf

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_laplace_origin_zero_of_normalised_small
import Theorems.Thm_AvramDividend_Classical_laplace_scaled_integral_tendsto
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_compensated_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_triplet_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_jump_split_integrable_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_large_jump_lower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_norm_lower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_gaussian_growth
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_jump_growth
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_superlinear
set_option autoImplicit false
open MeasureTheory Filter Set
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ¬ HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      W 0 0 = 0 := by
  intro Ω mΩ P hP D ψ W hψ hW hnbv
  let s : ℝ → ℝ := W 0
  have hs : IsQScale ψ 0 s := hW 0 le_rfl
  have hψ0 : ψ 0 = 0 := by
    have hh := hψ 0 1 (le_refl 0) (by norm_num)
    simpa [SpectrallyNegativeModel.toData] using hh.2
  have hlap : ∀ β : ℝ, 0 ≤ β → Phi ψ 0 < β →
      IntegrableOn (fun x : ℝ => Real.exp (-β * x) * s x) (Ioi 0) volume ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * s x ∂volume) = (ψ β)⁻¹ := by
    intro β hβ hΦβ
    simpa [s] using hs.2.2.2.2.2 β hβ hΦβ
  apply AvramDividend.Classical.laplace_origin_zero_of_normalised_small
    s ψ 0 (max 1 (Phi ψ 0) + 1) (fun x hx => hs.2.2.1 x) hs.2.2.2.2.1
  · intro β hβ hβpos
    have hphi : Phi ψ 0 < max 1 (Phi ψ 0) + 1 := by
      linarith [le_max_right (1 : ℝ) (Phi ψ 0)]
    simpa using hlap β (le_of_lt hβpos) (lt_of_lt_of_le hphi hβ)
  · intro ε hε
    rcases Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_superlinear
        P D ψ hψ hnbv (ε⁻¹ + 1) with ⟨β, hβone, hβbig⟩
    let θ : ℝ := max β (max 1 (Phi ψ 0) + 1)
    have hβθ : β ≤ θ := by
      dsimp [θ]
      exact le_max_left _ _
    have hcutθ : max 1 (Phi ψ 0) + 1 ≤ θ := by
      dsimp [θ]
      exact le_max_right _ _
    have hθone : 1 ≤ θ := hβone.trans hβθ
    have hθpos : 0 < θ := lt_of_lt_of_le zero_lt_one hθone
    have hCp : 0 < ε⁻¹ + 1 := by positivity
    have hmul : (ε⁻¹ + 1) * θ < ψ θ := by
      have hh := mul_lt_mul_of_pos_right (hβbig θ hβθ) hθpos
      simpa [div_mul_cancel₀ _ hθpos.ne'] using hh
    have hψpos : 0 < ψ θ := lt_of_lt_of_le (mul_pos hCp hθpos) hmul.le
    have hbig : ε⁻¹ * θ < ψ θ :=
      lt_trans (mul_lt_mul_of_pos_right (by linarith : ε⁻¹ < ε⁻¹ + 1) hθpos) hmul
    have htarget : θ < ε * ψ θ := by
      have hh := mul_lt_mul_of_pos_left hbig hε
      rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at hh
      exact hh
    have hdiv : θ / ψ θ < ε := (div_lt_iff₀ hψpos).2 htarget
    exact ⟨θ, hcutθ, hθpos, by simpa [hψ0, div_eq_mul_inv] using hdiv⟩
