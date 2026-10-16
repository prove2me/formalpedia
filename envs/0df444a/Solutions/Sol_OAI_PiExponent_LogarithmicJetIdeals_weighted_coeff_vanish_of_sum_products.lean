-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_sum_products
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:49:03.478016+00:00
-- url     : https://prove2.me/submissions/eb6ec6d3-a753-41fa-94a7-f8ccc6943b23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_coeff_vanish_of_product

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) (n : ℕ) (hn : 0 < n)
    (hv : ∀ i, 0 < v i)
    (φ : MvPolynomial (Fin (m + 1)) ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (hcoeff : ∀ (Q : MvPolynomial (Fin (m + 1)) ℂ), Q ∈ I →
      ∀ (a : Fin (m + 1) → ℕ),
        (∑ i, v i * (a i : ℝ)) < R →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (φ Q) = 0)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (s : Finset (MvPolynomial (Fin (m + 1)) ℂ ×
      (Fin n → MvPolynomial (Fin (m + 1)) ℂ)))
    (hrep : P = ∑ z ∈ s, z.1 * ∏ i, z.2 i)
    (hmem : ∀ z ∈ s, ∀ i, z.2 i ∈ I)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, v i * (a i : ℝ)) < (n : ℝ) * R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (φ P) = 0 := by
  classical
  rw [hrep]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro z hz
  exact OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_product
    v R n hn hv φ I hcoeff z.1 z.2 (fun i => hmem z hz i) a ha
