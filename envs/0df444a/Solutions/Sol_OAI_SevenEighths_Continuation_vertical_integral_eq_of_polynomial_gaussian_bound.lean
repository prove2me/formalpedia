-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.vertical_integral_eq_of_polynomial_gaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:53:23.924492+00:00
-- url     : https://prove2.me/submissions/17ba1516-424d-4f02-94cd-2f1a7820df07

import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationContour
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationPolynomialContour
import Theorems.Thm_OAI_SevenEighths_Continuation_polynomialGaussian_even
import Theorems.Thm_OAI_SevenEighths_Continuation_polynomialGaussian_integrable
import Theorems.Thm_OAI_SevenEighths_Continuation_polynomialGaussian_tendsto
import Theorems.Thm_OAI_SevenEighths_Continuation_vertical_integral_eq_of_even_envelope

set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.Continuation
namespace OAI.SevenEighths.Continuation
theorem _root_.solution (F : ℂ → ℂ)
    {a b C : ℝ} (n : ℕ) (hab : a ≤ b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ,
      ‖F ((x : ℂ)+y*I)‖ ≤ C*polynomialGaussian n y) :
    (∫ y : ℝ, F ((a : ℂ)+y*I)) = ∫ y : ℝ, F ((b : ℂ)+y*I) :=
  vertical_integral_eq_of_even_envelope F _ (polynomialGaussian_integrable n)
    (polynomialGaussian_even n) (polynomialGaussian_tendsto n) hab hhol hbound
end OAI.SevenEighths.Continuation
