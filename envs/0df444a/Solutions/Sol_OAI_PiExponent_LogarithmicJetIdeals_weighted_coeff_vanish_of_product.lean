-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_product
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:53:27.82999+00:00
-- url     : https://prove2.me/submissions/bcfc2927-68f5-4958-b3a7-4a4740b78fcc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_coeff_vanish_of_series_product

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
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (F : Fin n → MvPolynomial (Fin (m + 1)) ℂ)
    (hF : ∀ i, F i ∈ I)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, v i * (a i : ℝ)) < (n : ℝ) * R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (φ (Q * ∏ i, F i)) = 0 := by
  classical
  have hA : ∀ i (b : Fin (m + 1) → ℕ),
      (∑ j, v j * (b j : ℝ)) < R →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) (φ (F i)) = 0 := by
    intro i b hb
    exact hcoeff (F i) (hF i) b hb
  simpa only [map_mul, map_prod] using
    OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_series_product
      v R n hn hv (fun i => φ (F i)) (φ Q) hA a ha