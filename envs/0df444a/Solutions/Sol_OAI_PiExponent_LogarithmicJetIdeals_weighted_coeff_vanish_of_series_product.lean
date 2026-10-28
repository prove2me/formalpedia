-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_series_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:18:25.996651+00:00
-- url     : https://prove2.me/submissions/56bf37dd-ca92-4266-a6a9-070364910713

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

namespace S35W

def Van {m : ℕ} (v : Fin (m + 1) → ℝ) (W : ℝ) (f : MvPowerSeries (Fin (m + 1)) ℂ) : Prop :=
  ∀ x : Fin (m + 1) →₀ ℕ, (∑ j, v j * (x j : ℝ)) < W → MvPowerSeries.coeff x f = 0

theorem van_mul {m : ℕ} (v : Fin (m + 1) → ℝ) (W1 W2 : ℝ) (f g : MvPowerSeries (Fin (m + 1)) ℂ)
    (hf : Van v W1 f) (hg : Van v W2 g) : Van v (W1 + W2) (f * g) := by
  classical
  intro x hx
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hsum : (∑ j, v j * (x j : ℝ)) = (∑ j, v j * (p.1 j : ℝ)) + ∑ j, v j * (p.2 j : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hp, Finsupp.add_apply]; push_cast; ring
  by_cases h1 : (∑ j, v j * (p.1 j : ℝ)) < W1
  · rw [hf _ h1, zero_mul]
  · rw [hg p.2 (by linarith), mul_zero]

theorem van_zero {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ i, 0 < v i) (q : MvPowerSeries (Fin (m + 1)) ℂ) :
    Van v 0 q := by
  intro x hx
  exfalso
  have : 0 ≤ ∑ j, v j * (x j : ℝ) := Finset.sum_nonneg fun j _ => mul_nonneg (hv j).le (by positivity)
  linarith

end S35W

theorem solution
    {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) (n : ℕ) (hn : 0 < n)
    (hv : ∀ i, 0 < v i)
    (A : Fin n → MvPowerSeries (Fin (m + 1)) ℂ)
    (q : MvPowerSeries (Fin (m + 1)) ℂ)
    (hA : ∀ i (a : Fin (m + 1) → ℕ),
      (∑ j, v j * (a j : ℝ)) < R →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (A i) = 0)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ j, v j * (a j : ℝ)) < (n : ℝ) * R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (q * ∏ i, A i) = 0 := by
  have hA' : ∀ i, S35W.Van v R (A i) := by
    intro i x hx
    have := hA i (⇑x) hx
    simpa [InterpolationMatrix.exponentVector] using this
  have hprod : ∀ (s : Finset (Fin n)), S35W.Van v (s.card * R) (∏ i ∈ s, A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simpa using S35W.van_zero v hv 1
    | insert b s hb ih =>
      rw [Finset.prod_insert hb, Finset.card_insert_of_notMem hb]
      have := S35W.van_mul v R _ _ _ (hA' b) ih
      convert this using 1; push_cast; ring
  have := S35W.van_mul v 0 _ q _ (S35W.van_zero v hv q) (hprod Finset.univ)
  rw [Finset.card_univ, Fintype.card_fin, zero_add] at this
  exact this (InterpolationMatrix.exponentVector a) (by simpa [InterpolationMatrix.exponentVector] using ha)
