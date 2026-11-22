-- Prove2me | solution 1 for Kyprianou.Ch04.smallTimeDriftLimit
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T14:45:07.640075+00:00
-- url     : https://prove2.me/submissions/f0b56913-69e9-4010-bcfc-c9af596af116

import Theorems.Thm_AvramDividend_Classical_bv_actual_origin_dyadic_deficit_zero_ae_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_reciprocal_dyadic_mesh_cover_ws01c
import Theorems.Thm_AvramDividend_Classical_levy_linear_drift_shift_triplet_preserved_ws01f
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_driftpos_eventual_psi_above_no_standing_public
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_post_clock_positive_germ_of_dyadic_zero_no_standing_public

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option autoImplicit false

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 => L.X t ω / (t : ℝ))
        (nhdsWithin (0 : ℝ≥0) (Ioi 0)) (nhds L.drift) := by
  let δ : ℕ → ℝ≥0 := fun k => ((1 : ℝ≥0) / 2) ^ k
  have hδpos (k : ℕ) : 0 < δ k := by
    dsimp [δ]
    positivity
  have hRatio (k : ℕ) : (δ k : ℝ) ≤ 2 * (δ (k + 1) : ℝ) := by
    have hStep : (δ (k + 1) : ℝ) = (δ k : ℝ) * (1 / 2) := by
      simp [δ, pow_succ, mul_comm]
    rw [hStep]
    linarith
  let slope (n : ℕ) := L.drift - (1 / 2 : ℝ) ^ n
  have hLower (n : ℕ) : ∀ᵐ ω ∂P,
      ∃ ε : ℝ≥0, 0 < ε ∧ ∀ t : ℝ≥0, 0 < t → t < ε →
        slope n < L.X t ω / (t : ℝ) := by
    obtain ⟨Y, hPath, hPsi, hσ, hν⟩ :=
      levy_linear_drift_shift_triplet_preserved_ws01f L (slope n)
    have hYBV : Y.BoundedVariation := by
      simpa only [SpectrallyNegativeLevy.BoundedVariation, hσ, hν] using hBV
    have hc : Y.c = L.c - slope n := by
      have hAtOne := hPsi 1
      simp [SpectrallyNegativeLevy.ψ, laplaceExponent, hσ, hν] at hAtOne
      linarith
    have hYdrift : Y.drift = (1 / 2 : ℝ) ^ n := by
      rw [SpectrallyNegativeLevy.drift, hc, hν]
      dsimp [slope, SpectrallyNegativeLevy.drift]
      ring
    have hd : 0 < Y.drift := by rw [hYdrift]; positivity
    obtain ⟨B, hB, hLarge⟩ :=
      p2m81_bv_driftpos_eventual_psi_above_no_standing_public Y 1 one_pos hd hYBV
    let φ := B + 1
    have hφ : 0 < φ := by dsimp [φ]; linarith
    have hq : 0 < Y.ψ φ := one_pos.trans (hLarge φ (by dsimp [φ]; linarith))
    have hSlope : ∀ᵐ ω ∂P,
        Tendsto (fun k : ℕ =>
          (Y.drift * (δ k : ℝ) - (Y.X (0 + δ k) ω - Y.X 0 ω)) /
            (δ k : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [bv_actual_origin_dyadic_deficit_zero_ae_ws01c Y hYBV] with ω hω
      have hEq (k : ℕ) :
          (Y.drift * (δ k : ℝ) - (Y.X (0 + δ k) ω - Y.X 0 ω)) /
            (δ k : ℝ) = Y.drift - (Y.X (δ k) ω - Y.X 0 ω) / (δ k : ℝ) := by
        have hne : (δ k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hδpos k)
        rw [zero_add, sub_div, mul_div_cancel_right₀ _ hne]
      rw [funext hEq]
      simpa [δ] using hω
    filter_upwards [
      p2m81_bv_post_clock_positive_germ_of_dyadic_zero_no_standing_public
        Y (Y.ψ φ) φ hq hφ rfl hYBV (fun _ => 0) δ hδpos hRatio
        bv_reciprocal_dyadic_mesh_cover_ws01c hSlope] with ω hGerm
    obtain ⟨ε, hε, hPos⟩ := hGerm
    refine ⟨ε, hε, fun t ht htε => (lt_div_iff₀ (by exact_mod_cast ht)).mpr ?_⟩
    have htPos := hPos t ht htε
    simpa only [zero_add, Y.X_zero, sub_zero, hPath, sub_pos] using htPos
  filter_upwards [ae_all_iff.2 hLower, bv_drift_deficit_ae_monotone_all_times L hBV]
    with ω hLowerω hMonotone
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hb)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have hbs : b < slope n := by dsimp [slope]; linarith
    obtain ⟨ε, hε, hLocal⟩ := hLowerω n
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    exact hbs.trans (hLocal t ht.1 ht.2)
  · intro b hb
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have htPos : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t from ht)
    have hNonneg := hMonotone (show (0 : ℝ≥0) ≤ t from zero_le)
    have hBound : L.X t ω ≤ L.drift * (t : ℝ) := by
      simpa only [NNReal.coe_zero, mul_zero, L.X_zero, sub_self, sub_nonneg] using hNonneg
    exact ((div_le_iff₀ htPos).mpr hBound).trans_lt hb
