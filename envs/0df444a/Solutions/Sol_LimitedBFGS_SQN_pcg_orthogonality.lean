-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T12:57:07.150392+00:00
-- url     : https://prove2.me/submissions/f9db7a0b-f2fa-4cf5-8760-03cff3f279a2

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_joint_prefix_invariants

open Matrix
open LimitedBFGS.SQN

/-- Eq. (16), p. 777: along the preconditioned conjugate gradient iteration (13) with
fixed preconditioner `H0` and exact line searches, the gradients are mutually orthogonal
in the preconditioner-induced inner product for all distinct indices, and the gradient at
step `i` is orthogonal to every earlier search direction `d_j` with `j < i`.

**Reduction.** Both conjuncts are the one-sided prefix invariants of
`pcg_joint_prefix_invariants`, read off at the right index.

* The first conjunct is `G(i)` for `j < i` (already in the goal's own orientation) and
  `G(j)` exchanged through the symmetry of `H0` for `i < j`.
* The second conjunct *is* `D(i)`: the statement's side condition is literally `j < i`,
  so no case split and no symmetry are needed.

The direction recurrence plays no part here. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    (∀ i j, i ≠ j →
        grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x) = 0) ∧
      (∀ i j, j < i → grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d = 0) := by
  classical
  have hH_tr : H₀ᵀ = H₀ := (isHermitian_iff_isSymm.mp hH₀.isHermitian).eq
  have pair_comm_H : ∀ u v : Fin n → ℝ, u ⬝ᵥ (H₀ *ᵥ v) = v ⬝ᵥ (H₀ *ᵥ u) := by
    intro u v
    have h := dotProduct_transpose_mulVec (A := H₀) (x := u) (y := v)
    rwa [hH_tr] at h
  constructor
  · intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · calc grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ
          (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x)
        = grad A b (pcgIter A b H₀ x₀ j).x ⬝ᵥ
          (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ i).x) := pair_comm_H _ _
      _ = 0 := (pcg_joint_prefix_invariants A hA b H₀ hH₀ x₀ j).2.1 i hlt
    · exact absurd heq hij
    · exact (pcg_joint_prefix_invariants A hA b H₀ hH₀ x₀ i).2.1 j hgt
  · intro i j hji
    exact (pcg_joint_prefix_invariants A hA b H₀ hH₀ x₀ i).1 j hji
