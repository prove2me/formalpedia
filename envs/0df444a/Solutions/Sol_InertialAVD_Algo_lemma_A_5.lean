-- Prove2me | solution 1 for InertialAVD.Algo.lemma_A_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:44:29.040952+00:00
-- url     : https://prove2.me/submissions/dd3b6143-9ad9-4ec2-9d9a-2877e33315e9

import Mathlib
set_option autoImplicit false
open Filter Topology

theorem solution (α : ℝ) (hα : 3 ≤ α) (a ω : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hω : ∀ k, 0 ≤ ω k)
    (h : ∀ k : ℕ, 1 ≤ k → a (k + 1) ≤ ((k : ℝ) - 1) / ((k : ℝ) + α - 1) * a k + ω k)
    (hsum : Summable (fun k : ℕ => (k : ℝ) * ω k)) :
    Summable a := by
  -- multiplied form of the recursion, indexed by j = k - 1
  have hrec : ∀ j : ℕ, ((j : ℝ) + α) * a (j + 2) ≤ (j : ℝ) * a (j + 1) + ((j : ℝ) + α) * ω (j + 1) := by
    intro j
    have h1 := h (j + 1) (by omega)
    have hpos : 0 < (((j + 1 : ℕ) : ℝ) + α - 1) := by push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    have e : (((j + 1 : ℕ) : ℝ) + α - 1) = (j : ℝ) + α := by push_cast; ring
    have e2 : (((j + 1 : ℕ) : ℝ) - 1) = (j : ℝ) := by push_cast; ring
    rw [e, e2] at h1
    rw [e] at hpos
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : ((j : ℝ) + α) * ((j : ℝ) / ((j : ℝ) + α) * a (j + 1) + ω (j + 1))
        = (j : ℝ) * a (j + 1) + ((j : ℝ) + α) * ω (j + 1) := by
      field_simp
    have : a (j + 1 + 1) = a (j + 2) := rfl
    rw [this] at h2
    linarith
  have hQ : ∀ N : ℕ, (N : ℝ) * a (N + 1) + (α - 1) * ∑ j ∈ Finset.range N, a (j + 2)
      ≤ ∑ j ∈ Finset.range N, ((j : ℝ) + α) * ω (j + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have := hrec N
      push_cast
      nlinarith [this, ih]
  have hg : Summable (fun j : ℕ => ((j : ℝ) + α) * ω (j + 1)) := by
    have h1 : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ)) * ω (j + 1)) :=
      (summable_nat_add_iff 1).mpr hsum
    have h2 := h1.mul_left α
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) h2
    · exact mul_nonneg (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]) (hω _)
    · push_cast
      have : (j : ℝ) + α ≤ α * ((j : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
      calc ((j : ℝ) + α) * ω (j + 1) ≤ (α * ((j : ℝ) + 1)) * ω (j + 1) := mul_le_mul_of_nonneg_right this (hω _)
        _ = α * (((j : ℝ) + 1) * ω (j + 1)) := by ring
  have hb : Summable (fun j : ℕ => a (j + 2)) := by
    apply summable_of_sum_range_le (c := (∑' j : ℕ, ((j : ℝ) + α) * ω (j + 1)) / (α - 1))
    · intro j; exact ha _
    · intro N
      rw [le_div_iff₀ (by linarith)]
      have h1 := hQ N
      have h2 : ∑ j ∈ Finset.range N, ((j : ℝ) + α) * ω (j + 1)
          ≤ ∑' j : ℕ, ((j : ℝ) + α) * ω (j + 1) :=
        hg.sum_le_tsum _ (fun j _ => mul_nonneg (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]) (hω _))
      have h3 : 0 ≤ (N : ℝ) * a (N + 1) := mul_nonneg (Nat.cast_nonneg N) (ha _)
      nlinarith
  exact (summable_nat_add_iff 2).mp hb
