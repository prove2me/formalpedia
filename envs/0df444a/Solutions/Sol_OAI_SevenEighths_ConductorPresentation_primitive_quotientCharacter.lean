-- Prove2me | solution 1 for OAI.SevenEighths.ConductorPresentation.primitive_quotientCharacter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:16:09.796328+00:00
-- url     : https://prove2.me/submissions/04d9c181-1b1a-4be1-81cf-73eb9a2636d1

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_primitive_pullback


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
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (hφ : IsPrimitiveOnIdeals φ) :
    IsPrimitiveOnIdeals (quotientCharacter M I φ) :=
  CharacterTransport.primitive_pullback _ _ hφ
end OAI.SevenEighths.ConductorPresentation
