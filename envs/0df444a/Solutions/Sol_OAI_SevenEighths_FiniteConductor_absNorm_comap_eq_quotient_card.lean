-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.absNorm_comap_eq_quotient_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:43:47.190519+00:00
-- url     : https://prove2.me/submissions/82906f5a-5d46-4bfc-834f-7422d84f8604

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_quotient_comap_card

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (M : Ideal A) (I : Ideal (A ⧸ M)) :
    (I.comap (Ideal.Quotient.mk M)).cardQuot = Nat.card ((A ⧸ M) ⧸ I) := by
  simpa only [Submodule.cardQuot_apply] using quotient_comap_card M I
end OAI.SevenEighths.FiniteConductor
