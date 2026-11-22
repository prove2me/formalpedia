-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_le_one_public
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T12:13:11.618042+00:00
-- url     : https://prove2.me/submissions/fb843729-b088-44e0-a497-57398cbb31de

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

theorem solution (s : ℝ) (hs : 0 < s) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ) (hsupp : ρ (Iio (0 : ℝ)) = 0) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≤ 1 := by
  have hnonneg : ∀ᵐ y ∂ρ, y ∈ Ici (0 : ℝ) := by
    apply mem_ae_iff.mpr
    change ρ ((Ici (0 : ℝ))ᶜ) = 0
    rwa [compl_Ici]
  calc
    (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≤ ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [hnonneg] with y hy
      have hexp : Real.exp (-s * y) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (mem_Ici.mp hy))
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hexp
    _ = 1 := by simp
