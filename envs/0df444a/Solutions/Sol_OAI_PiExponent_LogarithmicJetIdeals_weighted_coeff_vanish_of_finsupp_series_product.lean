-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_finsupp_series_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:20:34.056659+00:00
-- url     : https://prove2.me/submissions/5899964e-9b4c-4a75-bc3b-9ab254fda89e

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

namespace E103WV

theorem key {m : ℕ} (v : Fin (m + 1) → ℝ) {n : ℕ} (T : Fin n → ℝ)
    (hv : ∀ j, 0 < v j)
    (A : Fin n → MvPowerSeries (Fin (m + 1)) ℂ)
    (hA : ∀ i (d : Fin (m + 1) →₀ ℕ),
      (∑ j, v j * (d j : ℝ)) < T i →
      MvPowerSeries.coeff d (A i) = 0)
    (s : Finset (Fin n)) : ∀ d : Fin (m + 1) →₀ ℕ,
      (∑ j, v j * (d j : ℝ)) < ∑ i ∈ s, T i →
      MvPowerSeries.coeff d (∏ i ∈ s, A i) = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro d hd
    simp only [Finset.sum_empty] at hd
    exfalso
    have : 0 ≤ ∑ j, v j * (d j : ℝ) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hv j).le (Nat.cast_nonneg _)
    linarith
  | insert k s hk ih =>
    intro d hd
    rw [Finset.prod_insert hk, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun pq hpq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    rw [Finset.sum_insert hk] at hd
    have hw : (∑ j, v j * (d j : ℝ)) =
        (∑ j, v j * (pq.1 j : ℝ)) + (∑ j, v j * (pq.2 j : ℝ)) := by
      rw [← Finset.sum_add_distrib, ← hpq]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add]
      ring
    by_cases h1 : (∑ j, v j * (pq.1 j : ℝ)) < T k
    · rw [hA k _ h1, zero_mul]
    · rw [ih _ (by linarith), mul_zero]

end E103WV

theorem solution
    {m : ℕ} (v : Fin (m + 1) → ℝ) (n : ℕ) (T : Fin n → ℝ)
    (hv : ∀ j, 0 < v j)
    (A : Fin n → MvPowerSeries (Fin (m + 1)) ℂ)
    (q : MvPowerSeries (Fin (m + 1)) ℂ)
    (hA : ∀ i (d : Fin (m + 1) →₀ ℕ),
      (∑ j, v j * (d j : ℝ)) < T i →
      MvPowerSeries.coeff d (A i) = 0)
    (hq : ∀ (d : Fin (m + 1) →₀ ℕ),
      (∑ j, v j * (d j : ℝ)) < 0 →
      MvPowerSeries.coeff d q = 0)
    (d : Fin (m + 1) →₀ ℕ)
    (hd : (∑ j, v j * (d j : ℝ)) < ∑ i, T i) :
    MvPowerSeries.coeff d (q * ∏ i, A i) = 0 := by
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  have hw : (∑ j, v j * (d j : ℝ)) =
      (∑ j, v j * (pq.1 j : ℝ)) + (∑ j, v j * (pq.2 j : ℝ)) := by
    rw [← Finset.sum_add_distrib, ← hpq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add]
    ring
  by_cases h1 : (∑ j, v j * (pq.1 j : ℝ)) < 0
  · rw [hq _ h1, zero_mul]
  · rw [E103WV.key v T hv A hA Finset.univ _ (by linarith), mul_zero]
