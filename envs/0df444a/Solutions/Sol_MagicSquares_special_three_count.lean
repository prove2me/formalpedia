-- Prove2me | solution 1 for MagicSquares.special_three_count
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:15:48.783979+00:00
-- url     : https://prove2.me/submissions/3b22d8c0-3c83-4745-992c-619d682376fd

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSpecial3
import Theorems.Thm_MagicSquares_pan_three_card
import Theorems.Thm_MagicSquares_symm_three_bij
import Theorems.Thm_MagicSquares_pan_three_otherwise
import Theorems.Thm_MagicSquares_symm_three_otherwise

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Solution for `MagicSquares.special_three_count`, the goal of Mission IV.

The count splits on whether the line sum `t` is divisible by three.

* If `3 ∣ t`, write `t = 3 * e`. Then `panMagicCount 3 (3*e) = 1` by
  `pan_three_card`, and
  `symmetricMagicCount 3 (3*e) = symmParamCount e = 2 * e + 1` by
  `symm_three_bij` composed with the cardinality of `symmParamSet e = range (2*e+1)`,
  using `(3 * e) / 3 = e`.
* If `3 ∤ t`, both counts vanish by `pan_three_otherwise` and
  `symm_three_otherwise`, which derive the divisibility obstruction from the
  centre identity `3 c = t` of `center_of_order_three`. -/
theorem solution (t : ℕ) :
    panMagicCount 3 t = (if 3 ∣ t then 1 else 0) ∧
      symmetricMagicCount 3 t = (if 3 ∣ t then 2 * (t / 3) + 1 else 0) := by
  by_cases h : 3 ∣ t
  · obtain ⟨e, rfl⟩ := h
    have h3 : (3 * e) / 3 = e := by
      rw [mul_comm 3 e]
      exact Nat.mul_div_left e (n := 3) (by norm_num)
    simp only [dvd_mul_right, if_true, h3]
    exact ⟨pan_three_card e, by
      rw [symm_three_bij, symmParamCount, symmParamSet, Finset.card_range]⟩
  · simp only [h, if_false]
    exact ⟨pan_three_otherwise t h, symm_three_otherwise t h⟩
