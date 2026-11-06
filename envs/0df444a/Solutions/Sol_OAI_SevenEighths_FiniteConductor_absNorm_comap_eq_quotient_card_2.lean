-- Prove2me | solution 2 for OAI.SevenEighths.FiniteConductor.absNorm_comap_eq_quotient_card
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:50.789798+00:00
-- url     : https://prove2.me/submissions/d4011dc5-5069-49c1-a205-b55bb07ae701

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite

theorem solution (M : Ideal A) (I : Ideal (A ⧸ M)) :
    (I.comap (Ideal.Quotient.mk M)).cardQuot = Nat.card ((A ⧸ M) ⧸ I) := by
  rw [Submodule.cardQuot_apply]
  exact Nat.card_congr (quotientComapEquiv M I).toEquiv
