-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_sum_lower_bound_of_exp_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T17:50:34.424859+00:00
-- url     : https://prove2.me/submissions/883f21ad-2eb9-4ca4-aaa2-d362f52418f0

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    {m n : ℕ} (wt : Fin (m + 1) → ℝ) (B : ℝ)
    (b : Fin n → Fin (m + 1) → ℕ) (a : Fin (m + 1) → ℕ)
    (hdecomp : (∑ i : Fin n, InterpolationMatrix.exponentVector (b i)) =
      InterpolationMatrix.exponentVector a)
    (hb : ∀ i : Fin n,
      B ≤ ∑ k : Fin (m + 1), wt k * (b i k : ℝ)) :
    (n : ℝ) * B ≤ ∑ k : Fin (m + 1), wt k * (a k : ℝ) := by
  have hcoord : ∀ k : Fin (m + 1), (∑ i : Fin n, b i k) = a k := by
    intro k
    have h := congrArg (fun f : Fin (m + 1) →₀ ℕ => f k) hdecomp
    simpa [InterpolationMatrix.exponentVector] using h
  have hcoord_real : ∀ k : Fin (m + 1),
      (∑ i : Fin n, (b i k : ℝ)) = (a k : ℝ) := by
    intro k
    exact_mod_cast hcoord k
  have hsum : (∑ i : Fin n, B) ≤
      ∑ i : Fin n, ∑ k : Fin (m + 1), wt k * (b i k : ℝ) :=
    Finset.sum_le_sum (fun i _ => hb i)
  calc
    (n : ℝ) * B ≤ ∑ i : Fin n, ∑ k : Fin (m + 1), wt k * (b i k : ℝ) := by
      simpa using hsum
    _ = ∑ k : Fin (m + 1), wt k * (a k : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.mul_sum]
      congr 1
      exact hcoord_real k