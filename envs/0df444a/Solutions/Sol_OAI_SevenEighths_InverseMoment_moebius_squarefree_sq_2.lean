-- Prove2me | solution 2 for OAI.SevenEighths.InverseMoment.moebius_squarefree_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:46.520479+00:00
-- url     : https://prove2.me/submissions/cac59fb4-7263-470f-9ca7-5450b3baa8bd

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
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {P : M} (hP : Squarefree P) :
    moebius P ^ 2 = 1 := by
  rw [hP.moebius_eq, ← pow_mul, mul_comm _ 2, pow_mul]
  norm_num
end OAI.SevenEighths.InverseMoment
