-- Prove2me | solution 1 for Kyprianou.Ch03.supInfDyadicGridArithmeticV1
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T11:29:24.43849+00:00
-- url     : https://prove2.me/submissions/0f1288dc-cb1d-449d-8b95-08d46f36f33b

import Mathlib

theorem solution (t : NNReal) (n : ℕ) :
    let q : Fin (2 ^ n + 1) → NNReal := fun i => ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)))
    Monotone q ∧ q 0 = 0 ∧ q (Fin.last (2 ^ n)) = t ∧
      (∀ i, q i ≤ t) ∧ ∀ i, q i.rev = t - q i := by
  dsimp only
  have h2 : ((2 ^ n : ℕ) : NNReal) ≠ 0 := by positivity
  have hc : ((2 ^ n : ℕ) : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)) = t := by field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    show (i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)) ≤
      (j.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))
    gcongr
    exact_mod_cast hij
  · simp
  · simpa [Fin.val_last] using hc
  · intro i
    have hi : (i.val : NNReal) ≤ ((2 ^ n : ℕ) : NNReal) := by
      exact_mod_cast Nat.le_of_lt_succ (Fin.is_lt i)
    calc (i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))
        ≤ ((2 ^ n : ℕ) : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)) := by gcongr
      _ = t := hc
  · intro i
    have hi : i.val ≤ 2 ^ n := Nat.le_of_lt_succ (Fin.is_lt i)
    have hsum : (i.rev.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)) +
        (i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)) = t := by
      rw [← add_mul]
      have hv : (i.rev.val : NNReal) + (i.val : NNReal) = ((2 ^ n : ℕ) : NNReal) := by
        have : i.rev.val + i.val = 2 ^ n := by
          rw [Fin.val_rev]
          omega
        exact_mod_cast this
      rw [hv, hc]
    exact eq_tsub_of_add_eq hsum
