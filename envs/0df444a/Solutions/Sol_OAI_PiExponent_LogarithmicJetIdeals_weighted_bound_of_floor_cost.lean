-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_bound_of_floor_cost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:39:20.960692+00:00
-- url     : https://prove2.me/submissions/1af2e9c1-e6a7-4aa7-84af-5aabaf93c06f

import Mathlib
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Real.Basic

open scoped BigOperators


theorem solution
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (ρ : ℝ) (a N : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hρ : 0 ≤ ρ)
    (ha : ∀ i, 0 < a i) (hN : ∀ i, 0 < N i)
    (hbudget : ∀ i, (N i : ℝ) * w i ≤ (a i : ℝ) * ρ)
    (k : ℕ) (u : ι → ℕ)
    (hcost : (∑ i, a i * (u i / N i)) < k) :
    (∑ i, w i * (u i : ℝ)) ≤
      (k : ℝ) * ρ + ∑ i, w i * ((N i - 1 : ℕ) : ℝ) := by
  have hkey : ∀ i, w i * (u i : ℝ) ≤ ((a i * (u i / N i) : ℕ) : ℝ) * ρ + w i * ((N i - 1 : ℕ) : ℝ) := by
    intro i
    have hdm := Nat.div_add_mod (u i) (N i)
    have hmod : u i % N i ≤ N i - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt _ (hN i))
    have hu : (u i : ℝ) = (N i : ℝ) * ((u i / N i : ℕ) : ℝ) + ((u i % N i : ℕ) : ℝ) := by
      exact_mod_cast hdm.symm
    have hm : ((u i % N i : ℕ) : ℝ) ≤ ((N i - 1 : ℕ) : ℝ) := by exact_mod_cast hmod
    have hq : (0 : ℝ) ≤ ((u i / N i : ℕ) : ℝ) := by positivity
    rw [hu]
    push_cast
    have h1 : w i * ((N i : ℝ) * ((u i / N i : ℕ) : ℝ)) ≤ (a i : ℝ) * ρ * ((u i / N i : ℕ) : ℝ) := by
      have := mul_le_mul_of_nonneg_right (hbudget i) hq
      linarith
    have h2 : w i * ((u i % N i : ℕ) : ℝ) ≤ w i * ((N i - 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hm (hw i)
    push_cast at h2
    nlinarith
  have hsum : (∑ i, a i * (u i / N i) : ℕ) ≤ k := hcost.le
  have hsumR : ((∑ i, a i * (u i / N i) : ℕ) : ℝ) ≤ k := by exact_mod_cast hsum
  calc (∑ i, w i * (u i : ℝ)) ≤ ∑ i, (((a i * (u i / N i) : ℕ) : ℝ) * ρ + w i * ((N i - 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum (fun i _ => hkey i)
    _ = ((∑ i, a i * (u i / N i) : ℕ) : ℝ) * ρ + ∑ i, w i * ((N i - 1 : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, Nat.cast_sum, Finset.sum_mul]
    _ ≤ _ := by gcongr

