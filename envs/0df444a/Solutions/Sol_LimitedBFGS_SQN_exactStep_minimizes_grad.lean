-- Prove2me | solution 1 for LimitedBFGS.SQN.exactStep_minimizes_grad
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T23:47:04.048257+00:00
-- url     : https://prove2.me/submissions/323f821c-4f7f-4e5e-824c-674fb6ec3056

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_quadratic

open Matrix
open LimitedBFGS.SQN

/-- The exact line search annihilates the gradient along the search direction.

`grad A b v = A *ᵥ v + b` is affine in `v`, so with `α = exactStep A b x d`

```lean
grad A b (x + α • d) ⬝ᵥ d = grad A b x ⬝ᵥ d + α * (d ⬝ᵥ (A *ᵥ d))
```

using `mulVec_add`, `mulVec_smul`, `add_dotProduct`, `dotProduct_add`,
`dotProduct_smul` and commutativity of the dot product. The right-hand factor is
exactly the denominator occurring in `exactStep`, and `α` is by definition
`-(grad A b x ⬝ᵥ d) / (d ⬝ᵥ A *ᵥ d)`, so the sum is `0`.

The only case analysis is on `d = 0`, where `exactStep` is `0 / 0 = 0` and the
whole expression collapses. In the nondegenerate case the denominator is
strictly positive because `A` is positive definite, which is what licenses the
cancellation. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b x d : Fin n → ℝ) :
    grad A b (x + exactStep A b x d • d) ⬝ᵥ d = 0 := by
  have hgrad : ∀ α : ℝ, grad A b (x + α • d) ⬝ᵥ d
      = grad A b x ⬝ᵥ d + α * (d ⬝ᵥ (A *ᵥ d)) := by
    intro α
    simp only [grad, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_add,
      Matrix.mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_smul,
      dotProduct_comm, one_mul, zero_mul, add_zero]
    ring
  rw [hgrad]
  by_cases hd : d = 0
  · -- Degenerate direction: everything collapses to `0`.
    simp [hd, exactStep]
  · -- Nondegenerate: the denominator is positive, so cancel it.
    have hpos : 0 < d ⬝ᵥ (A *ᵥ d) := hA.dotProduct_mulVec_pos hd
    rw [exactStep]
    field_simp [ne_of_gt hpos] <;> ring
