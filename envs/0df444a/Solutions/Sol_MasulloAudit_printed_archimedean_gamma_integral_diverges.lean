-- Prove2me | solution 1 for MasulloAudit.printed_archimedean_gamma_integral_diverges
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T06:24:43.473853+00:00
-- url     : https://prove2.me/submissions/003f1c62-8980-4093-9b85-b0d92d81d3e3

import Mathlib

open MeasureTheory

theorem solution (h : SchwartzMap ℝ ℝ) (hC : HasCompactSupport h) (h0 : 0 < h 0) (K : ℝ → ℝ) :
    let f := fun t : ℝ ↦ h 0/t-(h t+h (-t))*K t
    ∃ R > (0:ℝ), (∀ B ≥ R, (∫ t in R..B, f t) = h 0*Real.log (B/R)) ∧
      Filter.Tendsto (fun B : ℝ ↦ ∫ t in R..B, f t) Filter.atTop Filter.atTop ∧
      ¬IntegrableOn f (Set.Ioi (0:ℝ)) := by
  intro f
  obtain ⟨R, hR, hRz⟩ := hC.exists_pos_le_norm
  have hf : ∀ t, R ≤ t → f t = h 0 * t⁻¹ := by
    intro t ht
    have h1 : h t = 0 := hRz t (by rw [Real.norm_eq_abs]; exact le_trans ht (le_abs_self t))
    have h2 : h (-t) = 0 := hRz (-t) (by rw [Real.norm_eq_abs, abs_neg]; exact le_trans ht (le_abs_self t))
    simp only [f, h1, h2, add_zero, zero_mul, sub_zero, div_eq_mul_inv]
  have hint : ∀ B ≥ R, (∫ t in R..B, f t) = h 0 * Real.log (B / R) := by
    intro B hB
    have : (∫ t in R..B, f t) = ∫ t in R..B, h 0 * t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hB] at ht
      exact hf t ht.1
    rw [this, intervalIntegral.integral_const_mul, integral_inv_of_pos hR (lt_of_lt_of_le hR hB)]
  have htend : Filter.Tendsto (fun B : ℝ ↦ ∫ t in R..B, f t) Filter.atTop Filter.atTop := by
    have hlim : Filter.Tendsto (fun B : ℝ ↦ h 0 * Real.log (B / R)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop h0
        (Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const hR))
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop R] with B hB
    exact (hint B hB).symm
  refine ⟨R, hR, hint, htend, ?_⟩
  intro hI
  have hIR : IntegrableOn f (Set.Ioi R) := hI.mono_set (Set.Ioi_subset_Ioi hR.le)
  have := intervalIntegral_tendsto_integral_Ioi R hIR Filter.tendsto_id
  exact not_tendsto_nhds_of_tendsto_atTop htend _ this
