-- Prove2me | solution 1 for LimitedBFGS.SQN.pcgPair_y_eq
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:04:27.467797+00:00
-- url     : https://prove2.me/submissions/faa70bb4-1d46-43e5-bb0c-83c90839d3c3

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgPairs

open Matrix


open LimitedBFGS.SQN

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (k : ℕ) :
    (pcgPair A b H₀ x₀ k).2 = A *ᵥ (pcgPair A b H₀ x₀ k).1 := by
  rw [pcgPair, grad, grad]
  rw [Matrix.mulVec_sub]
  abel

