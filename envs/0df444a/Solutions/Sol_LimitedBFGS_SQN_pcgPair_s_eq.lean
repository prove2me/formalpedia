-- Prove2me | solution 1 for LimitedBFGS.SQN.pcgPair_s_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T22:48:08.372367+00:00
-- url     : https://prove2.me/submissions/44ae2c29-24b3-4e2e-88b8-15d276356b4f

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgPairs
import Definitions.Def_LimitedBFGS_SQN_sqnIter

open Matrix
open LimitedBFGS.SQN

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (k : ℕ) :
    (pcgPair A b H₀ x₀ k).1
      = exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d
          • (pcgIter A b H₀ x₀ k).d := by
  have hsucc : (pcgIter A b H₀ x₀ (k + 1)).x
      = (pcgIter A b H₀ x₀ k).x
        + exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d
          • (pcgIter A b H₀ x₀ k).d := by
    rw [pcgIter]
  have h1 : (pcgPair A b H₀ x₀ k).1
      = (pcgIter A b H₀ x₀ (k + 1)).x - (pcgIter A b H₀ x₀ k).x := rfl
  rw [h1, hsucc]
  abel
