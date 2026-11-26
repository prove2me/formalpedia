-- Prove2me | solution 1 for GlobalTheory.gaussAbs_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:39:43.330287+00:00
-- url     : https://prove2.me/submissions/998cb2f4-09f3-4564-b338-f30fe042a128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs

open GlobalTheory MvPolynomial
open scoped NNReal

variable {R σ : Type*} [CommRing R] [Nontrivial R]
variable (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)

theorem solution {f : MvPolynomial σ R} {r : ℝ} :
    gaussAbs a ha f ≤ r ↔ ∀ m, a (coeff m f) ≤ r := by
  constructor
  · intro h m
    have : a (coeff m f) = (absValuation a ha (coeff m f) : ℝ) :=
      (coe_absValuation a ha (coeff m f)).symm
    have hle := le_gaussVal (absValuation a ha) f m
    have : (absValuation a ha (coeff m f) : ℝ) ≤ gaussAbs a ha f := by
      simpa [gaussAbs_apply] using (NNReal.coe_le_coe.mpr hle)
    linarith
  · intro h
    by_cases hr : r < 0
    · have : 0 ≤ a (coeff (0 : σ →₀ ℕ) f) := a.nonneg _
      have := h (0 : σ →₀ ℕ)
      linarith
    · have hr0 : 0 ≤ r := le_of_not_gt hr
      let r' : ℝ≥0 := ⟨r, hr0⟩
      have h' : ∀ m, absValuation a ha (coeff m f) ≤ r' := by
        intro m
        exact NNReal.coe_le_coe.mp (by
          simpa [coe_absValuation, show (r' : ℝ) = r from rfl] using h m)
      have : gaussVal (absValuation a ha) f ≤ r' :=
        (gaussVal_le_iff (absValuation a ha)).mpr h'
      simpa [gaussAbs_apply, show (r' : ℝ) = r from rfl] using NNReal.coe_le_coe.mpr this
