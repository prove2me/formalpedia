-- Prove2me | solution 1 for Matrix.PosSemidef.exists_eq_sum_vecMulVec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:21.016032+00:00
-- url     : https://prove2.me/submissions/a5bf5cc0-a757-4cc0-8e2a-49776216c8b6

import Mathlib

-- carved verbatim out of submission 3c55ced4-4944-4de2-ba43-8110d2682db1, lines 1634-1644

section
open Matrix

theorem solution {n : Type*} [Fintype n] {Z : Matrix n n ℝ}
    (hZ : Z.PosSemidef) : ∃ z : n → n → ℝ, Z = ∑ j, vecMulVec (z j) (z j) := by
  classical
  open scoped MatrixOrder in
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.nonneg
  refine ⟨fun j => B j, ?_⟩
  ext a b
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply, star_eq_conjTranspose]

end
