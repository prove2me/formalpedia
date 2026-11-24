-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_interval_density_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T01:56:58.347121+00:00
-- url     : https://prove2.me/submissions/c2dfee13-ae47-46f1-a96d-acacbcedaa62

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_scale_transfer_public
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_bv_exit_ratio_no_standing_public
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio_unbounded_public
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponent_quadratic_upper
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_positive_from_quadratic
import Theorems.Thm_Kyprianou_Ch08_StageB_positiveRoot_scale_pos_on_positives
import Theorems.Thm_AvramDividend_Classical_corrected_exit_shifted_initial_reserve_monotone
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_Kyprianou_Ch03_spectrallyNegativePsi_zero
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem p2m87_qpos_interval_density_nonneg_core :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x y : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a → 0 ≤ y → y ≤ a →
      0 ≤ killedIntervalDensity (W q) a x y := by
  intro Ω mΩ P hP D ψ W hψ hW q a x y hq ha hx hxa hy0 hya
  have hWq : IsQScale ψ q (W q) := hW q (le_of_lt hq)
  have hneg := hWq.2.1
  have hnonneg := hWq.2.2.1
  obtain ⟨K, hK, hg⟩ := source_result81_exponent_quadratic_upper Ω P D ψ hψ
  have hWa : 0 < W q a := source_result81_scale_positive_from_quadratic ψ q (W q) hWq K hK hg a ha
  obtain ⟨F, A, hae, hAψ⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hnotneg : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω)) := by
    intro ha'
    have hd : ∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => D.X t ω) := by
      filter_upwards [hae, ha'] with ω h h'
      intro s t hst
      simpa [h s, h t] using h' hst
    exact D.excludesNegativeSubordinator hd
  have hscale : IsScaleFunction A q (W q) :=
    source_result81_upper_scale_transfer_public A ψ hAψ hnotneg q hq (W q) hWq
  have hrs : RightRootSet A.ψ q = RightRootSet ψ q := by
    ext β
    simp only [RightRootSet, mem_setOf_eq]
    constructor
    · rintro ⟨hβ, hr⟩
      exact ⟨hβ, by simpa [hAψ β hβ] using hr⟩
    · rintro ⟨hβ, hr⟩
      exact ⟨hβ, by rw [hAψ β hβ]; exact hr⟩
  have hPhi : Phi A.ψ q = Phi ψ q := by
    unfold Phi
    rw [hrs]
  have hrootA : PhiIsLargestRoot A.ψ q := by
    refine ⟨le_of_lt hq, ?_, ?_⟩
    · simpa [hPhi, hrs] using hWq.1.2.1
    · intro β hβ
      rw [hPhi]
      exact hWq.1.2.2 β (by simpa [hrs] using hβ)
  have hΦ0 : 0 ≤ Phi A.ψ q := hrootA.2.1.1
  have hΦroot : A.ψ (Phi A.ψ q) = q := hrootA.2.1.2
  have hΦpos : 0 < Phi A.ψ q := by
    have hne : Phi A.ψ q ≠ 0 := by
      intro hz
      have : A.ψ 0 = q := by simpa [hz] using hΦroot
      rw [Kyprianou.Ch03.spectrallyNegativePsi_zero P F A] at this
      linarith
    exact lt_of_le_of_ne hΦ0 (Ne.symm hne)
  by_cases hya_eq : y = a
  · subst y; unfold killedIntervalDensity
    by_cases hxa_eq : x = a
    · subst x; field_simp [hWa.ne']; ring_nf; norm_num
    · have hxne : x - a ≠ 0 := sub_ne_zero.mpr hxa_eq
      have hxlt : x - a < 0 := lt_of_le_of_ne (sub_nonpos.mpr hxa) hxne
      rw [hneg (x - a) hxlt]
      simpa using div_nonneg (mul_nonneg (hnonneg x) (hnonneg 0)) (le_of_lt hWa)
  · have hyla : y < a := lt_of_le_of_ne hya hya_eq
    by_cases hyx : y ≤ x
    · have hWay : 0 < W q (a - y) := positiveRoot_scale_pos_on_positives A q (Phi A.ψ q) hq hΦpos hΦroot (W q) hscale (a - y) (sub_pos.mpr hyla)
      have hc := corrected_exit_shifted_initial_reserve_monotone A q (a - x) (x - y) x (by linarith)
      have h1 : (a - x) + (x - y) = a - y := by ring
      have h2 : (a - x) + x = a := by ring
      have hc' : twoSidedExitExpectationCorrected A q (a - y) (x - y) ≤ twoSidedExitExpectationCorrected A q a x := by simpa [h1, h2] using hc
      have he : twoSidedExitExpectation A q (a - y) (x - y) ≤ twoSidedExitExpectation A q a x := by
        simpa [chat04_twoSidedExitExpectation_eq_corrected] using hc'
      have hENN : ENNReal.ofReal (W q (x - y) / W q (a - y)) ≤ ENNReal.ofReal (W q x / W q a) := by
        by_cases hBV : A.BoundedVariation
        · have hl := source_result81_bv_exit_ratio_no_standing_public A q (Phi A.ψ q) hq hΦpos hΦroot (W q) hscale hBV (a - y) (x - y) (sub_pos.mpr hyla) (sub_nonneg.mpr hyx) (by linarith)
          have hu := source_result81_bv_exit_ratio_no_standing_public A q (Phi A.ψ q) hq hΦpos hΦroot (W q) hscale hBV a x ha hx hxa
          simpa [hl, hu] using he
        · have hl := source_result81_upper_exit_ratio_unbounded_public A q hq (W q) hscale hBV (a - y) (x - y) (sub_pos.mpr hyla) (sub_nonneg.mpr hyx) (by linarith)
          have hu := source_result81_upper_exit_ratio_unbounded_public A q hq (W q) hscale hBV a x ha hx hxa
          simpa [hl, hu] using he
      have hratio : W q (x - y) / W q (a - y) ≤ W q x / W q a :=
        (ENNReal.ofReal_le_ofReal_iff (div_nonneg (hnonneg x) (le_of_lt hWa))).mp hENN
      have hm := mul_le_mul_of_nonneg_right hratio (le_of_lt hWay)
      have hl : (W q (x - y) / W q (a - y)) * W q (a - y) = W q (x - y) := by field_simp [hWay.ne']
      have hr : (W q x / W q a) * W q (a - y) = W q x * W q (a - y) / W q a := by ring
      rw [hl, hr] at hm
      unfold killedIntervalDensity
      linarith
    · have hxlt : x - y < 0 := by linarith
      unfold killedIntervalDensity
      rw [hneg (x - y) hxlt]
      simpa using div_nonneg (mul_nonneg (hnonneg x) (hnonneg (a - y))) (le_of_lt hWa)

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x y : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a → 0 ≤ y → y ≤ a →
      0 ≤ killedIntervalDensity (W q) a x y := by
  intro Ω mΩ P hP D ψ W hψ hW q a x y hq ha hx hxa hy hya
  exact p2m87_qpos_interval_density_nonneg_core Ω P D ψ W hψ hW q a x y hq ha hx hxa hy hya
