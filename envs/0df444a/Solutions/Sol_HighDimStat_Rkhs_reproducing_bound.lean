-- Prove2me | solution 1 for HighDimStat.Rkhs.reproducing_bound
-- status  : ACCEPTED   (disprove)
-- author  : @vebis
-- created : 2026-10-19T12:24:12.005487+00:00
-- url     : https://prove2.me/submissions/279cb506-20b2-4bf2-ba72-513efe264c93

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ {X : Type} (K : X → X → ℝ)
    (_hK : ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
      0 ≤ Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j)))),
    ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ) (z : X),
      abs (Finset.sum Finset.univ (fun i => c i * K z (x i))) ≤
        Real.sqrt (K z z) *
          Real.sqrt (Finset.sum Finset.univ (fun i =>
            Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j))))) := by
  intro h
  let K : Bool → Bool → ℝ := fun a b => ((a.toNat : ℝ)) - (b.toNat : ℝ)
  have hK : ∀ (n : ℕ) (x : Fin n → Bool) (c : Fin n → ℝ),
      0 ≤ Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j))) := by
    intro n x c
    have hs : Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j))) =
        - Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j))) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [K]
      ring
    linarith
  have := h K hK 1 (fun _ => false) (fun _ => 1) true
  have h1 : K true true = 0 := by simp [K]
  have h2 : K true false = 1 := by simp [K]
  have h3 : K false false = 0 := by simp [K]
  simp only [h1, h2, h3, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero,
    mul_one, one_mul, mul_zero, Real.sqrt_zero, abs_one, zero_mul] at this
  norm_num at this
