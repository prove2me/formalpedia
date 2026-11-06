-- Prove2me | solution 2 for OAI.SevenEighths.ConductorPresentation.comap_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:28.797425+00:00
-- url     : https://prove2.me/submissions/cbea7577-a9c6-4b61-b815-8e1de2545749

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
set_option autoImplicit false
open OAI
open OAI.SevenEighths
open OAI.SevenEighths.ConductorPresentation
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite

theorem solution (M : Ideal A) [Finite (A ⧸ M)] (I : Ideal (A ⧸ M)) :
    I.comap (Ideal.Quotient.mk M) ≠ ⊥ := by
  intro h
  have hM : M ≤ I.comap (Ideal.Quotient.mk M) := by
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have hM0 : M = ⊥ := le_bot_iff.mp (h ▸ hM)
  subst hM0
  have : Finite A := Finite.of_equiv _ (RingEquiv.quotientBot A).toEquiv
  exact not_finite A
