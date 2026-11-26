-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_stopped_cell_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:31:39.266792+00:00
-- url     : https://prove2.me/submissions/8ffe868e-e116-4d01-9959-939602f50dd9

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

/-- A stopped cell incurs its full-cell L1 error, plus a mesh charge only when cut. -/
theorem solution (H : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (a b t M δ : ℝ) (hab : a ≤ b) (hmesh : b-a ≤ δ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hHi : IntegrableOn H (Icc a b)) (hgi : IntegrableOn (fun s => g s b) (Icc a b))
    (hH : ∀ s ∈ Icc a b, |H s| ≤ M)
    (hg : ∀ s ∈ Icc a b, ∀ r ∈ Icc a b, |g s r| ≤ M) :
    |(∫ s in Icc (min t a) (min t b), H s) -
      ∫ s in Icc (min t a) (min t b), g s (min t b)| ≤
      (∫ s in Icc a b, |H s - g s b|) +
        if a < t ∧ t < b then 2*M*δ else 0 := by
  have hnon : 0 ≤ ∫ s in Icc a b, |H s - g s b| :=
    integral_nonneg fun s => abs_nonneg _
  by_cases ha : t ≤ a
  · simp [min_eq_left ha, min_eq_left (ha.trans hab), not_lt_of_ge ha, hnon]
  by_cases hb : b ≤ t
  · have ha' := hab.trans hb
    simp only [min_eq_right ha', min_eq_right hb, not_lt_of_ge hb, and_false, if_false, add_zero]
    rw [← integral_sub hHi hgi]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (μ := volume.restrict (Icc a b)) (fun s => H s - g s b)
  · have hat : a < t := lt_of_not_ge ha
    have htb : t < b := lt_of_not_ge hb
    simp only [min_eq_right hat.le, min_eq_left htb.le, hat, htb, and_self, if_true]
    have h1 : |∫ s in Icc a t, H s| ≤ M * (t-a) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hat.le]
      have hh : ∀ s ∈ Set.uIoc a t, ‖H s‖ ≤ M := by
        rw [Set.uIoc_of_le hat.le]
        intro s hs
        exact hH s ⟨hs.1.le,hs.2.trans htb.le⟩
      simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hat.le)] using
        intervalIntegral.norm_integral_le_of_norm_le_const hh
    have h2 : |∫ s in Icc a t, g s t| ≤ M * (t-a) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hat.le]
      have hh : ∀ s ∈ Set.uIoc a t, ‖g s t‖ ≤ M := by
        rw [Set.uIoc_of_le hat.le]
        intro s hs
        exact hg s ⟨hs.1.le,hs.2.trans htb.le⟩ t ⟨hat.le,htb.le⟩
      simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hat.le)] using
        intervalIntegral.norm_integral_le_of_norm_le_const hh
    have h3 := abs_sub_le (∫ s in Icc a t, H s) 0 (∫ s in Icc a t, g s t)
    simp only [sub_zero, zero_sub, abs_neg] at h3
    have h4 := mul_le_mul_of_nonneg_left (show t-a ≤ δ by linarith) hM
    linarith
