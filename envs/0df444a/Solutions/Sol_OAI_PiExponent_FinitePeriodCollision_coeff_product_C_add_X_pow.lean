-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.coeff_product_C_add_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:27:52.788735+00:00
-- url     : https://prove2.me/submissions/a6a474b9-238a-4687-95ee-5700e6334c1f

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coeff_product_coordinate_factors
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coeff_single_coordinate_binomial
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (a A : Fin m → ℕ) (b : Fin m → PowerSeries ℂ) :
    (∏ i, (MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff
        (InterpolationMatrix.exponentVector A) =
      PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
        ∏ i, (b i) ^ (a i - A i) := by
  rw [OAI.PiExponent.FinitePeriodCollision.coeff_product_coordinate_factors]
  simp_rw [OAI.PiExponent.FinitePeriodCollision.coeff_single_coordinate_binomial]
  simp [map_prod, Finset.prod_mul_distrib, mul_comm, mul_left_comm, mul_assoc]