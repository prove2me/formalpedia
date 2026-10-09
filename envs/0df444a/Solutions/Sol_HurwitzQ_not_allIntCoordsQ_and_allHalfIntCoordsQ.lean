-- Prove2me | solution 1 for HurwitzQ.not_allIntCoordsQ_and_allHalfIntCoordsQ
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-18T18:10:15.960346+00:00
-- url     : https://prove2.me/submissions/e54042c7-0988-46f4-8b57-150ce9eecd26

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Quaternion

open HurwitzQ


theorem solution (q : ℍ[ℚ]) :
    ¬ (allIntCoordsQ q ∧ allHalfIntCoordsQ q) := by
  rintro ⟨⟨a, b, c, d, hr, _, _, _⟩, ⟨a', b', c', d', hr', _, _, _⟩⟩
  have h : ((a - a' : ℤ) : ℚ) = 1 / 2 := by
    push_cast
    linarith [hr, hr']
  have h5 : ((1 : ℤ) : ℚ) = (2 : ℚ) * ↑(a - a') := by
    rw [h]
    norm_num
  obtain h6 : (1 : ℤ) = 2 * (a - a') := by exact_mod_cast h5
  omega


