-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.moebius_overlap_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:56.061594+00:00
-- url     : https://prove2.me/submissions/1f177e62-9ca0-438e-90f5-0a6619fc9ae6

import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Overlap
import Theorems.Thm_OAI_SevenEighths_InverseMoment_moebius_squarefree_sq

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open UniqueFactorizationMonoid
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {n P : M} (hnP : IsRelPrime n P)
    (hP : Squarefree P) : moebius n = moebius (n * P) * moebius P := by
  rw [hnP.moebius_mul, mul_assoc, ← pow_two, moebius_squarefree_sq hP, mul_one]
end OAI.SevenEighths.InverseMoment
