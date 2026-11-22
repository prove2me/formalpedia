-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_renewal_gap_algebra_identity_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T05:29:32.938796+00:00
-- url     : https://prove2.me/submissions/1d6a5501-e48a-4b72-8551-308a156ff1ec

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s) (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ) (heq : ∀ s : ℝ, 0 < s → (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal = f d * (1 - s / d)) (κ : Measure ℝ) (hκgen : ∀ s : ℝ, 0 < s → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) = ENNReal.ofReal d * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s) (hκform : ∀ s : ℝ, 0 < s → s ≠ d → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) = ENNReal.ofReal ((s * f d - d * f s) / (s * (f d - f s)))) (hRpos : ∀ s : ℝ, 0 < s → 0 < (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal) (hRle : ∀ s : ℝ, 0 < s → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal ≤ 1) (s : ℝ) (hs : 0 < s) : ENNReal.ofReal (d / f d) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ))⁻¹ = ENNReal.ofReal (s / f s) := by
  have hfd : 0 < f d := hpos d hd
  have hfd0 : f d ≠ 0 := ne_of_gt hfd
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hRtop : ∀ t : ℝ, 0 < t → (∫⁻ y, ENNReal.ofReal (Real.exp (-t * y)) ∂ρ) ≠ ⊤ := fun t ht hc => absurd (hRpos t ht) (by rw [hc, ENNReal.toReal_top]; exact lt_irrefl 0)
  have hReq : ∀ t : ℝ, 0 < t → (∫⁻ y, ENNReal.ofReal (Real.exp (-t * y)) ∂ρ) = ENNReal.ofReal ((∫⁻ y, ENNReal.ofReal (Real.exp (-t * y)) ∂ρ).toReal) := fun t ht => (ENNReal.ofReal_toReal (hRtop t ht)).symm
  by_cases hsd : s = d
  · rw [hsd]
    set R : ℝ := (∫⁻ y, ENNReal.ofReal (Real.exp (-d * y)) ∂ρ).toReal with hRdef
    have hRrpos : 0 < R := hRpos d hd
    have hnn2 : 0 ≤ 1 - R := sub_nonneg.mpr (hRle d hd)
    have h1R : (1:ℝ≥0∞) - ENNReal.ofReal R = ENNReal.ofReal (1 - R) := by rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (le_of_lt hRrpos)]
    rw [hReq d hd, ← hRdef, hκgen d hd, hReq d hd, ← hRdef, h1R]
    simp only [div_eq_mul_inv]
    rw [← ENNReal.ofReal_inv_of_pos hd, ← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_mul (mul_nonneg hd.le hnn2)]
    have hr1 : d * (1 - R) * d⁻¹ = 1 - R := by field_simp
    rw [hr1]
    have h1r : (1:ℝ≥0∞) - ENNReal.ofReal (1 - R) = ENNReal.ofReal R := by rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hnn2]; congr 1; ring
    rw [h1r, ← ENNReal.ofReal_inv_of_pos hRrpos, ← ENNReal.ofReal_mul (mul_nonneg hd.le (inv_nonneg.mpr hfd.le)), ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hd.le (inv_nonneg.mpr hfd.le)) (le_of_lt hRrpos))]
    congr 1
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hRrpos), mul_one]
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
    rw [hReq s hs, ← hRdef, hκform s hs hsd, ← hvdef, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hvnn, ← ENNReal.ofReal_inv_of_pos h1vpos, ← ENNReal.ofReal_mul (div_nonneg hd.le hfd.le), ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg hd.le hfd.le) (le_of_lt hRrpos))]
    have hgoal : (d / f d) * R * (1 - v)⁻¹ = s / f s := by rw [hRreq, h1v]; field_simp
    rw [hgoal]
