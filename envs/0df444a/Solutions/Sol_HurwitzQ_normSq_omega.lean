-- Prove2me | solution 1 for HurwitzQ.normSq_omega
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-18T18:10:13.669326+00:00
-- url     : https://prove2.me/submissions/7938cb2e-e083-45b4-847b-90b4b072fcb9

import Definitions.Def_HurwitzQ_omega
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.NormNum

open Quaternion

open HurwitzQ


theorem solution : normSq omega = 1 := by
  rw [normSq_def']
  show ((1 : ℚ) / 2) ^ 2 + (1 / 2) ^ 2 + (1 / 2) ^ 2 + (1 / 2) ^ 2 = 1
  norm_num


