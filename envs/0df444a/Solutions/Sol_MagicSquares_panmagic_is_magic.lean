-- Prove2me | solution 1 for MagicSquares.panmagic_is_magic
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T14:06:16.677603+00:00
-- url     : https://prove2.me/submissions/adcee60a-0e2c-4975-9055-cbf9b14b4f2a

import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Direct proof of `MagicSquares.panmagic_is_magic`.

`IsPanMagic M s` asserts the semi-magic condition together with the statement that
*every* broken diagonal in both directions sums to `s`. The two main diagonals are
the broken diagonals of offset `0`, so `IsMagic M s` follows at once. -/
theorem solution {n : ℕ} [NeZero n] (M : Square n ℕ) (s : ℕ) (hP : IsPanMagic M s) :
    IsMagic M s := by
  constructor
  · exact hP.1
  constructor
  · simpa [diagSum, brokenDiagSum] using hP.2.1 (0 : Fin n)
  · simpa [antiDiagSum, brokenAntiDiagSum] using hP.2.2 (0 : Fin n)
