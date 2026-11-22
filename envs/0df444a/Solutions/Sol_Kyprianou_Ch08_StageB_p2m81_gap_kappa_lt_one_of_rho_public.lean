-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_gap_kappa_lt_one_of_rho_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T05:45:18.024865+00:00
-- url     : https://prove2.me/submissions/7689d0e5-7bc2-4ebf-bafa-47f2e2ab107e

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (heq : ∀ s : ℝ, 0 < s →
      (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
        f d * (1 - s / d))
    (κ : Measure ℝ) [SFinite κ]
    (hκgen : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
        ENNReal.ofReal d * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s)
    (hκform : ∀ s : ℝ, 0 < s → s ≠ d →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
        ENNReal.ofReal ((s * f d - d * f s) / (s * (f d - f s))))
    (hR : ∀ s : ℝ, 0 < s →
      0 < (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ∧
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≤ 1) :
    ∀ s : ℝ, 0 < s → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) < 1 := by
  intro s hs
  have hfd : 0 < f d := hpos d hd
  have hfd0 : f d ≠ 0 := ne_of_gt hfd
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hRtop : ∀ t : ℝ, 0 < t → (∫⁻ y, ENNReal.ofReal (Real.exp (-t * y)) ∂ρ) ≠ ⊤ :=
    fun t ht => ne_of_lt (lt_of_le_of_lt (hR t ht).2 ENNReal.one_lt_top)
  have hRpos : ∀ t : ℝ, 0 < t → 0 < (∫⁻ y, ENNReal.ofReal (Real.exp (-t * y)) ∂ρ).toReal :=
    fun t ht => ENNReal.toReal_pos (ne_of_gt (hR t ht).1) (hRtop t ht)
  have hRle : ∀ t : ℝ, 0 < t → (∫⁻ y, ENNReal.ofReal (Real.exp (-t * y)) ∂ρ).toReal ≤ 1 :=
    fun t ht => by simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (hR t ht).2
  have hReq : ∀ t : ℝ, 0 < t → (∫⁻ y, ENNReal.ofReal (Real.exp (-t * y)) ∂ρ) = ENNReal.ofReal ((∫⁻ y, ENNReal.ofReal (Real.exp (-t * y)) ∂ρ).toReal) := fun t ht => (ENNReal.ofReal_toReal (hRtop t ht)).symm
  by_cases hsd : s = d
  · rw [hsd]
    set R : ℝ := (∫⁻ y, ENNReal.ofReal (Real.exp (-d * y)) ∂ρ).toReal with hRdef
    have hRrpos : 0 < R := hRpos d hd
    have hnn2 : 0 ≤ 1 - R := sub_nonneg.mpr (hRle d hd)
    have h1R : (1:ℝ≥0∞) - ENNReal.ofReal R = ENNReal.ofReal (1 - R) := by rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (le_of_lt hRrpos)]
    have hr1 : d * (1 - R) * d⁻¹ = 1 - R := by field_simp
    rw [hκgen d hd, hReq d hd, ← hRdef, h1R]
    simp only [div_eq_mul_inv]
    rw [← ENNReal.ofReal_inv_of_pos hd, ← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_mul (mul_nonneg hd.le hnn2), hr1, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn2]
    linarith [hRrpos]
  · have heqs := heq s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hfs0 : f s ≠ 0 := ne_of_gt (hpos s hs)
    have hsd1 : s / d ≠ 1 := by intro hc; apply hsd; field_simp at hc; linarith
    have hAne : f d - f s ≠ 0 := by intro hcon; rw [hcon, zero_mul] at heqs; exact (mul_ne_zero hfd0 (sub_ne_zero.mpr (Ne.symm hsd1))) heqs.symm
    set R : ℝ := (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal with hRdef
    have hRrpos : 0 < R := hRpos s hs
    have h1eq : (1:ℝ) - s / d = (d - s) / d := by rw [sub_div, div_self hd0]
    rw [h1eq] at heqs
    field_simp at heqs
    have hRreq : R = f d * (d - s) / (d * (f d - f s)) := by field_simp; linarith [heqs]
    have hBA : (d - s) / (f d - f s) = d * R / f d := by field_simp; linarith [heqs]
    set v : ℝ := (s * f d - d * f s) / (s * (f d - f s)) with hvdef
    have hv2 : (s * f d - d * f s) / (s * (f d - f s)) = d * (1 - R) / s := by rw [hRreq]; field_simp; ring
    have hvnn : 0 ≤ d * (1 - R) / s := div_nonneg (mul_nonneg hd.le (sub_nonneg.mpr (hRle s hs))) hs.le
    rw [← hv2, ← hvdef] at hvnn
    have hsub : (f s * (d - s)) / (s * (f d - f s)) = (f s / s) * ((d - s) / (f d - f s)) := by field_simp
    have hsubpos : 0 < (f s / s) * (d * R / f d) := mul_pos (div_pos (hpos s hs) hs) (div_pos (mul_pos hd hRrpos) hfd)
    rw [← hBA, ← hsub] at hsubpos
    have h1v : 1 - v = f s * (d - s) / (s * (f d - f s)) := by rw [hvdef]; field_simp; ring
    have h1vpos : 0 < 1 - v := by linarith [h1v, hsubpos]
    rw [hκform s hs hsd, ← hvdef, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hvnn]
    linarith [h1vpos]
