-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_grad_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T12:56:11.723265+00:00
-- url     : https://prove2.me/submissions/37ce272d-5324-45e1-96f0-358113e57e42

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_joint_prefix_invariants

open Matrix
open LimitedBFGS.SQN

/-- Eq. (16), p. 777, first relation: the gradients of the preconditioned conjugate
gradient iteration (13) with fixed preconditioner `H0` are mutually orthogonal in the
preconditioner-induced inner product, for all indices.

**Reduction.** This is the one-sided prefix invariant `G` of
`pcg_joint_prefix_invariants`, read in both orientations; the two orientations differ by
the symmetry of `H0`. The proof contains no recurrence of its own: it invokes the joint
invariant, splits `i ≠ j` into the two orderings, and closes each ordering with the
corresponding field of `G` (the first directly, the second after swapping the two
arguments through `pair_comm_H`).

Symmetry of the preconditioner comes from `hH0 : H0.PosDef`, which makes `H0` Hermitian
and therefore symmetric, combined with `dotProduct_transpose_mulVec`. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∀ i j, i ≠ j →
      grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ
        (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x) = 0 := by
  classical
  have hH_tr : H₀ᵀ = H₀ := (isHermitian_iff_isSymm.mp hH₀.isHermitian).eq
  have pair_comm_H : ∀ u v : Fin n → ℝ, u ⬝ᵥ (H₀ *ᵥ v) = v ⬝ᵥ (H₀ *ᵥ u) := by
    intro u v
    have h := dotProduct_transpose_mulVec (A := H₀) (x := u) (y := v)
    rwa [hH_tr] at h
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  -- `i < j`: `G(j)` supplies the *swapped* pair, so the symmetry of `H₀` is needed.
  · calc grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ
          (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x)
      = grad A b (pcgIter A b H₀ x₀ j).x ⬝ᵥ
          (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ i).x) := pair_comm_H _ _
    _ = 0 := (pcg_joint_prefix_invariants A hA b H₀ hH₀ x₀ j).2.1 i hlt
  · exact absurd heq hij
  -- `j < i`: `G(i)` is already in the goal's own orientation.
  · exact (pcg_joint_prefix_invariants A hA b H₀ hH₀ x₀ i).2.1 j hgt
