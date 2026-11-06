-- Prove2me | solution 1 for OAI.SevenEighths.ConductorPresentation.quotientCharacter_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:39:29.150395+00:00
-- url     : https://prove2.me/submissions/48d1d7a5-7b86-4652-af8f-f643e24a2fb6

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
variable {A : Type*} [CommRing A]
namespace OAI.SevenEighths.ConductorPresentation
theorem _root_.solution (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (a : A) :
    quotientCharacter M I φ (Ideal.Quotient.mk _ a) =
      φ (Ideal.Quotient.mk I (Ideal.Quotient.mk M a)) := rfl
end OAI.SevenEighths.ConductorPresentation
