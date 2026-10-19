-- Prove2me | solution 1 for Giddings1999.twoH_indicial_roots
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:38:39.189216+00:00
-- url     : https://prove2.me/submissions/73c09e6f-11f3-4239-bfe7-cea53e48c476

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology
open Giddings1999

theorem solution (d : ℕ) (m R : ℝ) :
    twoHPlus d m R * (twoHPlus d m R - d) = m ^ 2 * R ^ 2 ∧
    twoHMinus d m R * (twoHMinus d m R - d) = m ^ 2 * R ^ 2 ∧
    twoHPlus d m R - twoHMinus d m R = 2 * nu d m R := by
  have hs : Real.sqrt ((d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2) ^ 2 = (d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2 :=
    Real.sq_sqrt (by positivity)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [twoHPlus, twoHMinus, nu] <;> nlinarith [hs]
