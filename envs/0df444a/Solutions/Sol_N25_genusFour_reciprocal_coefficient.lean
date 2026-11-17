-- Prove2me | solution 1 for N25.genusFour_reciprocal_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:50.966277+00:00
-- url     : https://prove2.me/submissions/bcb29e36-1d55-4e2e-b325-f1c590839f5b

import Definitions.Def_N25_GenusFourNumerator

/-! # Reconstruction from four counts and the genus-four functional equation

The hypotheses retain the degree bound, constant coefficient, Newton identities,
and functional equation explicitly. Geometric producers of these hypotheses are
separate from this integer-polynomial calculation.
-/

namespace N25

/-- The scaled functional equation implies its first-half coefficient rule. -/
theorem _root_.solution
    {L : Polynomial ℤ} {q : ℤ} (hq : q ≠ 0)
    (hrec : ∀ i ≤ 8, L.coeff (8 - i) * q ^ i = q ^ 4 * L.coeff i)
    (i : ℕ) (hi : i ≤ 4) :
    L.coeff (8 - i) = q ^ (4 - i) * L.coeff i := by
  apply mul_right_cancel₀ (pow_ne_zero i hq)
  calc
    L.coeff (8 - i) * q ^ i = q ^ 4 * L.coeff i := hrec i (by omega)
    _ = (q ^ (4 - i) * L.coeff i) * q ^ i := by
      rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel hi]

namespace Endgame

end Endgame

end N25
