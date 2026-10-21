-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.binomial_exp_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:47:26.46765+00:00
-- url     : https://prove2.me/submissions/c793fa06-ed96-44e3-b0e0-aa5741fbde00

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (x b : Fin m → ℝ)
    (hx : ∀ i, 0 ≤ x i) (h : ∀ i, x i ≤ Real.exp (b i)) :
    (∏ i, x i) ≤ Real.exp (∑ i, b i) := by
  calc
    (∏ i, x i) ≤ ∏ i, Real.exp (b i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact hx i
      · intro i hi
        exact h i
    _ = Real.exp (∑ i, b i) := by
      rw [← Real.exp_sum]