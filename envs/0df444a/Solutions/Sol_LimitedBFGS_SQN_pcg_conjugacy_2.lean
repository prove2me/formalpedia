-- Prove2me | solution 2 for LimitedBFGS.SQN.pcg_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T12:57:22.857618+00:00
-- url     : https://prove2.me/submissions/26d47f7d-7609-4df8-b520-2e19ab224115

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_joint_prefix_invariants

open Matrix
open LimitedBFGS.SQN

/-- Eq. (15), p. 777 — the conjugacy condition along the preconditioned conjugate gradient
iteration (13) of Nocedal 1980 with fixed preconditioner `H0` and exact line searches:

    d_i ᵀ y_j = 0   for all i ≠ j,   where y_j = g_{j+1} - g_j.

**Reduction.** Because the gradient of the quadratic is affine and `x_{j+1}` is by
definition `x_j + a_j • d_j` with `a_j = exactStep A b x_j d_j`, the increment of the
gradient along the step is exactly

    y_j = g_{j+1} - g_j = a_j • (A *ᵥ d_j),

so `d_i ⬝ᵥ y_j = a_j * (d_i ⬝ᵥ (A *ᵥ d_j))`, and the full-index `A`-conjugacy of the
directions makes the parenthesised factor zero.

**Why no case split.** The step coefficient `a_j` is never divided by. It appears only as
a multiplicative factor on a term that is already zero, so the degenerate `a_j = 0` case
— which arises in exact-rational simulation and which would defeat a proof that cancels
`a_j` to read `A *ᵥ d_j` back from `y_j` — needs no separate treatment at all. For the same
reason no assumption on the step, and no statement about termination, is required.

The `A`-conjugacy of the directions is the one-sided prefix invariant `C` of
`pcg_joint_prefix_invariants`, read at the larger of the two indices. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) (i j : ℕ) (hij : i ≠ j) :
    (pcgIter A b H₀ x₀ i).d ⬝ᵥ
      (grad A b (pcgIter A b H₀ x₀ (j + 1)).x - grad A b (pcgIter A b H₀ x₀ j).x) = 0 := by
  classical
  have hgrad (k : ℕ) :
      grad A b (pcgIter A b H₀ x₀ (k + 1)).x
        = grad A b (pcgIter A b H₀ x₀ k).x
          + exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d
            • (A *ᵥ (pcgIter A b H₀ x₀ k).d) := by
    have hx : (pcgIter A b H₀ x₀ (k + 1)).x
        = (pcgIter A b H₀ x₀ k).x
          + exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d
            • (pcgIter A b H₀ x₀ k).d := by simp only [pcgIter]
    have haff (a : ℝ) (x d : Fin n → ℝ) :
        grad A b (x + a • d) = grad A b x + a • (A *ᵥ d) := by
      simp only [grad, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      abel
    rw [hx, haff]
  -- `y_j = g_{j+1} - g_j = a_j • (A *ᵥ d_j)`.
  have hy : grad A b (pcgIter A b H₀ x₀ (j + 1)).x - grad A b (pcgIter A b H₀ x₀ j).x
      = exactStep A b (pcgIter A b H₀ x₀ j).x (pcgIter A b H₀ x₀ j).d
        • (A *ᵥ (pcgIter A b H₀ x₀ j).d) := by rw [hgrad j, add_sub_cancel_left]
  have hA_tr : Aᵀ = A := (isHermitian_iff_isSymm.mp hA.isHermitian).eq
  have pair_comm_A : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
    intro u v
    have h := dotProduct_transpose_mulVec (A := A) (x := u) (y := v)
    rwa [hA_tr] at h
  -- Full-index `A`-conjugacy from the one-sided prefix invariant `C`.
  have hconj : (pcgIter A b H₀ x₀ i).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ j).d) = 0 := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · calc (pcgIter A b H₀ x₀ i).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ j).d)
        = (pcgIter A b H₀ x₀ j).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ i).d) := pair_comm_A _ _
      _ = 0 := (pcg_joint_prefix_invariants A hA b H₀ hH₀ x₀ j).2.2 i hlt
    · exact absurd heq hij
    · exact (pcg_joint_prefix_invariants A hA b H₀ hH₀ x₀ i).2.2 j hgt
  rw [hy, dotProduct_smul, smul_eq_mul, hconj, mul_zero]
