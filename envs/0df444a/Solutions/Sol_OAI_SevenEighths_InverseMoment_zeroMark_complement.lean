-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.zeroMark_complement
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:09:54.519204+00:00
-- url     : https://prove2.me/submissions/75ed2559-652a-4312-b653-21941980aaf8

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_LocalReflection
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]
omit [Fintype F]

theorem solution (x : F) :
    zeroMark x = 1 - (1 : MulChar F ℂ) x := by
  by_cases hx : x = 0
  · subst x
    simp [zeroMark, MulChar.map_zero]
  · simp [zeroMark, hx, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
