-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_pow_bound_of_zero_constant
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:08:55.787007+00:00
-- url     : https://prove2.me/submissions/e1acd36a-bd9d-4f3c-bbd3-98a63a3edb3b

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_bound_of_zero_constant

open scoped BigOperators

theorem solution {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → PowerSeries ℂ) (m : σ → ℕ) (k : ℕ)
    (h0 : ∀ i, PowerSeries.coeff 0 (f i) = 0)
    (h1 : ∀ i n, ‖PowerSeries.coeff n (f i)‖ ≤ (1 : ℝ)) :
    ‖PowerSeries.coeff k (∏ i, f i ^ (m i : ℕ))‖ ≤ (2 : ℝ) ^ k := by
  let τ := Σ i, Fin (m i)
  let g : τ → PowerSeries ℂ := fun x => f x.1
  have hg0 : ∀ x, PowerSeries.coeff 0 (g x) = 0 := by
    intro x
    exact h0 x.1
  have hg1 : ∀ x n, ‖PowerSeries.coeff n (g x)‖ ≤ (1 : ℝ) := by
    intro x n
    exact h1 x.1 n
  have hbound :=
    OAI.PiExponent.MatrixTranslationBounds.coeff_prod_bound_of_zero_constant
      (g := g) k hg0 hg1
  simpa [g, τ, Fintype.prod_sigma] using hbound