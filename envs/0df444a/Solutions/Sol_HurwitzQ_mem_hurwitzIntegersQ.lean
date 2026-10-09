-- Prove2me | solution 1 for HurwitzQ.mem_hurwitzIntegersQ
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-18T18:10:10.123122+00:00
-- url     : https://prove2.me/submissions/38c2fdd1-dcc7-4caf-be9c-fd4b2f8fa589

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Ring

open Quaternion

open HurwitzQ


@[simp]
theorem solution (q : ℍ[ℚ]) :
    q ∈ hurwitzIntegersQ ↔ allIntCoordsQ q ∨ allHalfIntCoordsQ q :=
  Iff.rfl


