-- Prove2me | solution 1 for Milne.zeta_point
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-21T13:02:08.114566+00:00
-- url     : https://prove2.me/submissions/7021164c-ccfa-47e5-b963-c1220e1b2774

import Definitions.Def_Milne_zeta
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Daily21Milne

/-- For one point over every extension field, each prefix of the recursively
constructed zeta coefficient sequence is the constant function one. -/
theorem point_prefix (n k : ℕ) : Milne.zetaSeq (fun _ => (1 : ℚ)) n k = 1 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      simp only [Milne.zetaSeq]
      split
      · exact ih k
      · simp only [ih, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        have hn : (n + 1 : ℚ) ≠ 0 := by positivity
        simpa only [Nat.cast_add, Nat.cast_one] using (div_self hn)

end Daily21Milne

/-- The zeta function of a point has every Taylor coefficient equal to one. -/
theorem solution (n : ℕ) : Milne.zetaCoeff (fun _ => (1 : ℚ)) n = 1 := by
  exact Daily21Milne.point_prefix (n + 1) n

#print axioms solution
