-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.coeff_product_coordinate_factors
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:31:19.724989+00:00
-- url     : https://prove2.me/submissions/a5ee0ff3-6b90-414e-8563-39d9cea283fe

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coordinate_factor_support
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coeff_prod_single_coordinate_support
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (a A : Fin m → ℕ) (b : Fin m → PowerSeries ℂ) :
    (∏ i, (MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff
        (InterpolationMatrix.exponentVector A) =
      ∏ i, ((MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff
        (Finsupp.single i (A i)) := by
  have hs := OAI.PiExponent.FinitePeriodCollision.coordinate_factor_support a b
  simpa [InterpolationMatrix.exponentVector] using
    (OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_support
      (σ := Fin m) (R := PowerSeries ℂ)
      (f := fun i => (MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i) A hs)