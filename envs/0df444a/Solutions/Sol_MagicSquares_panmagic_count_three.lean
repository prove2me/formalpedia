-- Prove2me | solution 1 for MagicSquares.panmagic_count_three
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-18T15:38:20.305501+00:00
-- url     : https://prove2.me/submissions/2a214129-5cee-4ad0-9e5c-70f4c0b1dbb5

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresPandiagonal
import Theorems.Thm_MagicSquares_pan_three_card
import Theorems.Thm_MagicSquares_pan_three_otherwise

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Solution for `MagicSquares.panmagic_count_three`: the two-direction reading gives `1` exactly when `3 | t`. Contrast with `pandiagonal_count_three`, which counts the one-direction reading of BCCG and never vanishes. -/
theorem solution (t : ℕ) : panMagicCount 3 t = if 3 ∣ t then 1 else 0 := by
  by_cases h : 3 ∣ t
  · obtain ⟨e, rfl⟩ := h
    rw [if_pos (dvd_mul_right 3 e)]
    exact pan_three_card e
  · rw [if_neg h]
    exact pan_three_otherwise t h
