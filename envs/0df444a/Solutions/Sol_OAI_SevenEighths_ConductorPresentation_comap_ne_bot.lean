-- Prove2me | solution 1 for OAI.SevenEighths.ConductorPresentation.comap_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:50.965389+00:00
-- url     : https://prove2.me/submissions/db99ad24-662a-4cf0-9459-2b585625aafc

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_absNorm_comap_eq_quotient_card


set_option autoImplicit false
open OAI
open OAI.SevenEighths
open OAI.SevenEighths.ConductorPresentation
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
namespace OAI.SevenEighths.ConductorPresentation
theorem _root_.solution (M : Ideal A) [Finite (A ⧸ M)] (I : Ideal (A ⧸ M)) :
    I.comap (Ideal.Quotient.mk M) ≠ ⊥ := by
  let : Finite ((A ⧸ M) ⧸ I) :=
    Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hpos : 0 < (I.comap (Ideal.Quotient.mk M)).cardQuot := by
    rw [absNorm_comap_eq_quotient_card]
    exact Nat.card_pos
  intro hzero
  rw [hzero, Submodule.cardQuot_bot] at hpos
  exact (lt_irrefl 0) hpos
end OAI.SevenEighths.ConductorPresentation
