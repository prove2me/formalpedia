-- Prove2me | solution 1 for Kyprianou.Ch04.squareL2IntegralEqNnnorm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:11:44.811943+00:00
-- url     : https://prove2.me/submissions/37e48fa7-57a5-48bf-85d7-38536b3a4b89

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false
universe u

/-- Convert a finite real squared integral into an ENNReal squared-norm lintegral. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ)
    (hInt : Integrable (fun ω => (Z ω) ^ 2) P) :
    ∫ ω, (Z ω) ^ 2 ∂P =
      (∫⁻ ω, ((‖Z ω‖₊ : ℝ≥0∞) ^ 2) ∂P).toReal := by
  have hsquare (x : ℝ) :
      ENNReal.ofReal (x ^ 2) = ((‖x‖₊ : ℝ≥0∞) ^ 2) := by
    rw [← sq_abs x, ENNReal.ofReal_pow (abs_nonneg x)]
    rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg x)]
    rw [← Real.nnnorm_abs x, Real.nnnorm_of_nonneg (abs_nonneg x)]
  calc
    ∫ ω, (Z ω) ^ 2 ∂P =
        (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P).toReal := by
      exact integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun ω => sq_nonneg (Z ω)))
        hInt.aestronglyMeasurable
    _ = (∫⁻ ω, ((‖Z ω‖₊ : ℝ≥0∞) ^ 2) ∂P).toReal := by
      congr 1
      apply lintegral_congr
      intro ω
      exact hsquare (Z ω)
