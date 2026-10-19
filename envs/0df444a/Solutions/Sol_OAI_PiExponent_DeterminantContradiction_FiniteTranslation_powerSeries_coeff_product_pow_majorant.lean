-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.powerSeries_coeff_product_pow_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:13:32.023617+00:00
-- url     : https://prove2.me/submissions/7428c387-eefa-4002-aada-b45ee3253bf2

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_coefficientwise_majorant_products

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {m : ℕ} (L : PowerSeries ℂ) (B : Fin m → PowerSeries ℂ)
    (q : Fin m → ℕ) (k : ℕ)
    (hL : ∀ n, ∃ x : ℝ, 0 ≤ x ∧ PowerSeries.coeff n L = (x : ℂ))
    (hB : ∀ i n, ‖PowerSeries.coeff n (B i)‖ ≤ ‖PowerSeries.coeff n L‖) :
    ‖PowerSeries.coeff k (∏ i : Fin m, B i ^ q i)‖ ≤
      ‖PowerSeries.coeff k (L ^ (∑ i : Fin m, q i))‖ := by
  have h := coefficientwise_majorant_products
    (C := fun _ : Fin m => L) (B := B) (q := q) (k := k)
    (hC := by intro i n; exact hL n) (hB := hB)
  simpa [Finset.prod_pow_eq_pow_sum] using h