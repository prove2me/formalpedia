-- Prove2me | solution 1 for OAI.SevenEighths.ResidueCharacter.inflate_apply_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:42:35.170007+00:00
-- url     : https://prove2.me/submissions/bab0fca5-accd-41d0-824f-ba0feebb25f4

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ResidueCharacter
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]
namespace OAI.SevenEighths.ResidueCharacter
theorem _root_.solution {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (u : (A ⧸ M)ˣ) :
    inflate hML χ u = χ (Ideal.Quotient.factor hML (u : A ⧸ M)) :=
  MulChar.ofUnitHom_coe _ u
end OAI.SevenEighths.ResidueCharacter
