-- Prove2me | solution 1 for MarkovChainCLT.abs_setAverage_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:14:35.161392+00:00
-- url     : https://prove2.me/submissions/b2757539-eb94-4df0-8a03-97a84bf4ece3

import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

/-- If `h` stays within `C` of `m` on `s`, so does its average over `s`. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (s : Set Ω) (hs : MeasurableSet s) (hρs : ρ s ≠ 0)
    (h : Ω → ℝ) (hint : IntegrableOn h s ρ) (m C : ℝ)
    (hbd : ∀ u ∈ s, |h u - m| ≤ C) :
    |(∫ u in s, h u ∂ρ) / (ρ s).toReal - m| ≤ C := by
  have hfin : ρ s ≠ ∞ := measure_ne_top ρ s
  have hpos : 0 < (ρ s).toReal := ENNReal.toReal_pos hρs hfin
  have hconst : ∀ c : ℝ, (∫ _u in s, c ∂ρ) = (ρ s).toReal * c := by
    intro c
    rw [integral_const, smul_eq_mul]
    congr 1
    simp [Measure.real, Measure.restrict_apply_univ]
  have hsub : IntegrableOn (fun u => h u - m) s ρ := hint.sub (integrable_const m).restrict
  have hcent : (∫ u in s, (h u - m) ∂ρ)
      = (∫ u in s, h u ∂ρ) - (ρ s).toReal * m := by
    rw [integral_sub hint (integrable_const m).restrict, hconst]
  have hbound : |∫ u in s, (h u - m) ∂ρ| ≤ C * (ρ s).toReal := by
    have h1 : |∫ u in s, (h u - m) ∂ρ| ≤ ∫ u in s, |h u - m| ∂ρ := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ρ.restrict s)
        (f := fun u => h u - m)
    have h2 : (∫ u in s, |h u - m| ∂ρ) ≤ ∫ _u in s, C ∂ρ := by
      refine integral_mono_ae hsub.abs (integrable_const C).restrict ?_
      filter_upwards [ae_restrict_mem hs] with u hu
      exact hbd u hu
    rw [hconst] at h2
    calc |∫ u in s, (h u - m) ∂ρ| ≤ ∫ u in s, |h u - m| ∂ρ := h1
      _ ≤ (ρ s).toReal * C := h2
      _ = C * (ρ s).toReal := by ring
  have hkey : (∫ u in s, h u ∂ρ) / (ρ s).toReal - m
      = (∫ u in s, (h u - m) ∂ρ) / (ρ s).toReal := by
    rw [hcent]
    field_simp
  rw [hkey, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  linarith [hbound]
