-- Prove2me | solution 2 for OAI.SevenEighths.InverseMoment.moebius_overlap_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:37.747883+00:00
-- url     : https://prove2.me/submissions/2feb3792-6a03-4087-a7bc-248b82a51ad8

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

theorem solution {n P : M} (hnP : IsRelPrime n P)
    (hP : Squarefree P) : moebius n = moebius (n * P) * moebius P := by
  rw [hnP.moebius_mul, mul_assoc, hP.moebius_eq, ← mul_pow]
  norm_num
