-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.absNorm_inf_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:43:05.685426+00:00
-- url     : https://prove2.me/submissions/f6b7aac3-2f20-47f5-9d4b-4d78cd88281f

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_quotient_inf_card_le_mul

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    (I ⊓ J).cardQuot ≤ I.cardQuot * J.cardQuot := by
  simpa only [Submodule.cardQuot_apply] using
    quotient_inf_card_le_mul I J
end OAI.SevenEighths.FiniteConductor
