-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_direction_base
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T07:34:04.85598+00:00
-- url     : https://prove2.me/submissions/b31fd4c7-22e8-402b-8bf4-46805bd6fb5d

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix
open LimitedBFGS.SQN

/-- The base case of the downward induction that carries eq. (16)'s second relation:
the initial direction is exactly `d_0 = -(H0 *ᵥ g_0)`, so for every nonzero `i`,

    g_i ⬝ᵥ d_0  =  -(g_i ⬝ᵥ (H0 *ᵥ g_0)).

Together with the already-proved child `pcg_direction_recursion`, which gives the
step from `j - 1` to `j`, this is all that is needed to read
`LimitedBFGS.SQN.pcg_orthogonality`'s second conjunct as a downward induction on
`j` from its first. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (i : ℕ) (hne : i ≠ 0) :
    grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (pcgIter A b H₀ x₀ 0).d
      = -(grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ
            (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ 0).x)) := by
  have h0 : pcgIter A b H₀ x₀ 0 = ⟨x₀, -(H₀ *ᵥ grad A b x₀)⟩ := by
    simp [pcgIter]
  rw [h0]
  simp only [dotProduct_neg]
