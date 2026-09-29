-- Prove2me | solution 1 for MagicSquares.affine_preserves_magic
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:29:28.683816+00:00
-- url     : https://prove2.me/submissions/15725f36-b2f3-4782-91da-67124bdda980

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Every line has `n` entries, so its sum becomes `a * s + n • b`. -/
theorem solution {n : ℕ} {α : Type*} [Semiring α]
    (M : Square n α) (s a b : α) (hM : IsMagic M s) :
    IsMagic (affine a b M) (a * s + n • b) := by
  constructor
  · constructor
    · intro i
      simpa [rowSum_affine, hM.1.1 i]
    · intro j
      simpa [colSum_affine, hM.1.2 j]
  · constructor
    · simpa [diagSum_affine, hM.2.1]
    · simpa [antiDiagSum_affine, hM.2.2]
