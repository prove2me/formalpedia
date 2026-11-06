-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.moebius_squarefree_sq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:58:33.020916+00:00
-- url     : https://prove2.me/submissions/6a50caa7-0664-4ebc-86ab-c84d919d8c31

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
  rw [hP.moebius_eq, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
