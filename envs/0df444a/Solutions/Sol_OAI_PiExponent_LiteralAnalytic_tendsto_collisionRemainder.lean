-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.tendsto_collisionRemainder
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T15:25:31.382984+00:00
-- url     : https://prove2.me/submissions/83747f2e-1c55-43a7-b970-5a54752fe3df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_log_actualRowCount_div_tendsto

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem solution {nu : Real} (d : FixedData nu) :
    Tendsto (fun H : Real => Collision.collisionRemainder (actualRowCount d H) H) atTop (nhds 0) := by
  have hlog := OAI.PiExponent.LiteralAnalytic.log_actualRowCount_div_tendsto d
  have hconst : Tendsto (fun H : Real =>
      (Real.log 2 / 4 - Real.log (1 - OAI.PiExponent.Collision.collisionRatio)) / H)
      atTop (nhds 0) := tendsto_id.const_div_atTop _
  have hsum := hlog.add hconst
  have hEq : (fun H : Real => Collision.collisionRemainder (actualRowCount d H) H) =
      (fun H => Real.log (actualRowCount d H : Real) / H +
        (Real.log 2 / 4 - Real.log (1 - OAI.PiExponent.Collision.collisionRatio)) / H) := by
    funext H
    simp only [OAI.PiExponent.Collision.collisionRemainder]
    ring
  rw [hEq]
  simpa only [add_zero] using hsum
