-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.DiscCover.const_coord
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:20:08.659449+00:00
-- url     : https://prove2.me/submissions/8eeb979b-7e9a-40bb-b8b3-30ef8a9d9f47

import Mathlib


theorem solution (y : Fin 1 → ℂ) : (fun _ : Fin 1 => y 0) = y := by
  funext i; exact congrArg y (Subsingleton.elim 0 i)
