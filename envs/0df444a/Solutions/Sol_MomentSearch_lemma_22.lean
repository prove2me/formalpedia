-- Prove2me | solution 1 for MomentSearch.lemma_22
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T22:35:38.739256+00:00
-- url     : https://prove2.me/submissions/a7e22e72-d2da-4bb4-9440-0da7aed0b344

import Mathlib
import Definitions.Def_MomentSearch_moment
import Definitions.Def_MomentSearch_grid

open scoped BigOperators
open MomentSearch

private lemma affine_vanishing {n : ℕ} (x : Fin n → ℝ) (c d : ℝ)
    (i : ℕ) (a : Fin n → ℝ)
    (h : ∀ j : ℕ, j ≤ i → ∑ t : Fin n, a t * x t ^ j = 0) :
    ∑ t : Fin n, a t * (c * x t + d) ^ i = 0 := by
  induction i generalizing a with
  | zero => simpa using h 0 (by omega)
  | succ i ih =>
    have h₀ := ih a (fun j hj => h j (Nat.le_trans hj (Nat.le_succ i)))
    have h₁ := ih (fun t => a t * x t) (by
      intro j hj
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
        h (j + 1) (Nat.succ_le_succ hj))
    calc
      ∑ t : Fin n, a t * (c * x t + d) ^ (i + 1) =
          c * (∑ t : Fin n, (a t * x t) * (c * x t + d) ^ i) +
          d * (∑ t : Fin n, a t * (c * x t + d) ^ i) := by
            simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro t _
            ring
      _ = 0 := by rw [h₀, h₁]; ring

theorem solution {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (∀ a : Fin n → ℝ,
      (∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * ((t : ℕ) : ℝ) ^ i = 0) ↔
        (∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * grid n (t : ℕ) ^ i = 0)) ∧
    (∀ p p' : Fin n → ℝ, p ∈ stdSimplex ℝ (Fin n) → p' ∈ stdSimplex ℝ (Fin n) →
      ((∀ i : ℕ, i ≤ k → moment p i = moment p' i) ↔
        (∀ i : ℕ, i ≤ k →
          ∑ t : Fin n, p t * grid n (t : ℕ) ^ i = ∑ t : Fin n, p' t * grid n (t : ℕ) ^ i))) := by
  have hn' : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have equivalence : ∀ a : Fin n → ℝ,
      (∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * ((t : ℕ) : ℝ) ^ i = 0) ↔
      (∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * grid n (t : ℕ) ^ i = 0) := by
    intro a
    constructor
    · intro h i hi
      have h' := affine_vanishing (fun t : Fin n => ((t : ℕ) : ℝ))
        (2 / ((n : ℝ) - 1)) (-1) i a
        (fun j hj => h j (Nat.le_trans hj hi))
      simpa only [grid, div_eq_mul_inv, sub_eq_add_neg, mul_assoc,
        mul_left_comm, mul_comm] using h'
    · intro h i hi
      have h' := affine_vanishing (fun t : Fin n => grid n (t : ℕ))
        (((n : ℝ) - 1) / 2) (((n : ℝ) - 1) / 2) i a
        (fun j hj => h j (Nat.le_trans hj hi))
      have inverse (t : Fin n) :
          (((n : ℝ) - 1) / 2) * grid n (t : ℕ) +
            (((n : ℝ) - 1) / 2) = ((t : ℕ) : ℝ) := by
        dsimp [grid]
        field_simp [hn']
        ring
      simpa only [inverse] using h'
  refine ⟨equivalence, ?_⟩
  intro p p' _ _
  simpa only [moment, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using
    equivalence (fun t => p t - p' t)
