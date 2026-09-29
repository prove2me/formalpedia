-- Prove2me | solution 1 for MagicSquares.semi_magic_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-20T14:55:47.93173+00:00
-- url     : https://prove2.me/submissions/b67b135f-bf4e-46d1-b4a9-14dd91d176dd

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_semi_magic_polynomial_exists
import Theorems.Thm_MagicSquares_semi_magic_reciprocity
import Theorems.Thm_MagicSquares_semi_magic_vanishing

set_option autoImplicit false

open MagicSquares

/-- Conditional root reduction for live mission-goal theorem
`a8fa7ac8-321b-492a-9e96-d5303081a54f`.  The imported local mirrors stand for
the three live milestones; this file itself contains no placeholder. -/
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        (∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) ∧
          (∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ))
            = (-1 : ℚ) ^ (n - 1) * p.eval ((t : ℤ) : ℚ)) ∧
            (∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0) := by
  obtain ⟨p, hdeg, hp⟩ := MagicSquares.semi_magic_polynomial_exists n hn
  exact ⟨p, hdeg, hp,
    MagicSquares.semi_magic_reciprocity n hn p hp,
    MagicSquares.semi_magic_vanishing n hn p hp⟩
