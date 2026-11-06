-- Prove2me | solution 3 for OAI.SevenEighths.InverseMoment.moebius_squarefree_sq
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:20.747604+00:00
-- url     : https://prove2.me/submissions/0617f9ec-c951-4e52-8742-898432d3350b

import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Overlap
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open UniqueFactorizationMonoid
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
theorem solution {P : M} (hP : Squarefree P) :
    moebius P ^ 2 = 1 := by
  rw [Squarefree.moebius_eq hP, ← pow_mul, mul_comm, pow_mul]
  norm_num
