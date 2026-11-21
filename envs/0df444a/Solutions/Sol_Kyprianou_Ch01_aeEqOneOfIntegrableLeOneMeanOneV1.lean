-- Prove2me | solution 1 for Kyprianou.Ch01.aeEqOneOfIntegrableLeOneMeanOneV1
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T02:41:26.732501+00:00
-- url     : https://prove2.me/submissions/22f3c803-bcb4-4237-b0c8-609cd48eaa4d

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ)
    (hf : Integrable f P)
    (hfLe : ∀ᵐ ω ∂P, f ω ≤ 1)
    (hMean : (∫ ω, f ω ∂P) = 1) :
    ∀ᵐ ω ∂P, f ω = 1 := by
  have hg : Integrable (fun x => 1 - f x) P := (integrable_const (1 : ℝ)).sub hf
  have hn : ∀ᵐ x ∂P, 0 ≤ 1 - f x := hfLe.mono fun x hx => sub_nonneg.mpr hx
  have hz : (∫ x, (1 - f x) ∂P) = 0 := by
    rw [integral_sub (integrable_const (1 : ℝ)) hf, hMean]
    simp
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hn hg).mp hz] with x hx
  exact (sub_eq_zero.mp hx).symm
