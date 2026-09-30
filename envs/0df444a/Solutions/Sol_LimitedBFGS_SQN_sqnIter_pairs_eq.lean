-- Prove2me | solution 1 for LimitedBFGS.SQN.sqnIter_pairs_eq
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:39:49.983439+00:00
-- url     : https://prove2.me/submissions/3a30f22b-aaa2-4f6c-97b0-3278f4620236

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgPairs
import Definitions.Def_LimitedBFGS_SQN_sqnIter

open Matrix
open LimitedBFGS.SQN

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (x₀ : Fin n → ℝ) (k : ℕ)
    (hx : ∀ j ≤ k, (sqnIter A b H₀ m x₀ j).x = (pcgIter A b H₀ x₀ j).x) :
    (sqnIter A b H₀ m x₀ k).pairs = pcgPairs A b H₀ x₀ m k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' : (sqnIter A b H₀ m x₀ k).pairs = pcgPairs A b H₀ x₀ m k :=
      ih (fun j hj => hx j (le_trans hj (Nat.le_succ k)))
    have h1 : (sqnIter A b H₀ m x₀ (k+1)).x = (pcgIter A b H₀ x₀ (k+1)).x :=
      hx (k+1) le_rfl
    have h0 : (sqnIter A b H₀ m x₀ k).x = (pcgIter A b H₀ x₀ k).x :=
      hx k (Nat.le_succ k)
    have hpair : (((sqnIter A b H₀ m x₀ (k+1)).x - (sqnIter A b H₀ m x₀ k).x,
        grad A b (sqnIter A b H₀ m x₀ (k+1)).x - grad A b (sqnIter A b H₀ m x₀ k).x)
        : (Fin n → ℝ) × (Fin n → ℝ)) = pcgPair A b H₀ x₀ k := by
      rw [h1, h0]
      rfl
    have hstep : (sqnIter A b H₀ m x₀ (k+1)).pairs
        = (((sqnIter A b H₀ m x₀ k).pairs ++
            [((sqnIter A b H₀ m x₀ (k+1)).x - (sqnIter A b H₀ m x₀ k).x,
             grad A b (sqnIter A b H₀ m x₀ (k+1)).x
               - grad A b (sqnIter A b H₀ m x₀ k).x)]).drop
          (((sqnIter A b H₀ m x₀ k).pairs ++
            [((sqnIter A b H₀ m x₀ (k+1)).x - (sqnIter A b H₀ m x₀ k).x,
             grad A b (sqnIter A b H₀ m x₀ (k+1)).x
               - grad A b (sqnIter A b H₀ m x₀ k).x)]).length - m)) := rfl
    have hrec : pcgPairs A b H₀ x₀ m (k+1)
        = ((pcgPairs A b H₀ x₀ m k ++ [pcgPair A b H₀ x₀ k]).drop
          ((pcgPairs A b H₀ x₀ m k ++ [pcgPair A b H₀ x₀ k]).length - m)) := rfl
    rw [hstep, hrec, ih', hpair]
