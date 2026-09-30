-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_grad_direction_backward
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:47:40.910674+00:00
-- url     : https://prove2.me/submissions/117ac5e3-2b28-4fed-bd2e-54a8734530f7

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_orthogonality

open Matrix
open LimitedBFGS.SQN

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∀ i j : ℕ, j < i →
      grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d = 0 :=
  (pcg_orthogonality A hA b H₀ hH₀ x₀).2
