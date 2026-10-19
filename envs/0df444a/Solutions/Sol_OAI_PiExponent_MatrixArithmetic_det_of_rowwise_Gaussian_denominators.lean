-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.det_of_rowwise_Gaussian_denominators
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:13:14.774999+00:00
-- url     : https://prove2.me/submissions/0618e5be-ed2e-4b7c-87da-4ed7a23169fb

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators
theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (d : ι → ℕ) (b : ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (hentry : ∀ i j, ∃ g : GaussianInt, (d i : ℂ) * M i j = (g : ℂ))
    (hlog : ∀ i, Real.log (d i : ℝ) ≤ b i) :
    ∃ D : ℕ, 0 < D ∧
      ∃ g : GaussianInt, (D : ℂ) * M.det = (g : ℂ) ∧
        Real.log (D : ℝ) ≤ ∑ i, b i := by
  choose G hG using hentry
  refine ⟨∏ i, d i, Finset.prod_pos (fun i _ => hd i), (Matrix.of G).det, ?_, ?_⟩
  · have h1 : Matrix.diagonal (fun i => (d i : ℂ)) * M = (Matrix.of G).map GaussianInt.toComplex := by
      ext i j
      simp [Matrix.diagonal_mul, hG]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_diagonal, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
    push_cast
    exact h2
  · push_cast
    rw [Real.log_prod (fun i _ => by have := hd i; positivity)]
    exact Finset.sum_le_sum (fun i _ => hlog i)
