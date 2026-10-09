-- Prove2me | solution 1 for HurwitzQ.omega_sq
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-18T18:10:18.804298+00:00
-- url     : https://prove2.me/submissions/e3767947-51a2-4135-89ba-fa2ea82c41f9

import Definitions.Def_HurwitzQ_omega
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.NormNum

open Quaternion

open HurwitzQ


theorem solution : omega ^ 2 = omega - 1 := by
  rw [sq]
  ext <;> simp <;> norm_num [omega]


