-- Prove2me | solution 1 for OAI.SevenEighths.ResidueCharacter.inflate_toUnitHom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:46.488078+00:00
-- url     : https://prove2.me/submissions/a662b08c-22e6-49fa-bb72-87885e012ac8

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_apply
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_mul
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_symm
attribute [local simp] OAI.SevenEighths.ConductorPresentation.quotientCharacter_mk



set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ResidueCharacter
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]
namespace OAI.SevenEighths.ResidueCharacter
theorem _root_.solution {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    (inflate hML χ).toUnitHom =
      χ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hML).toMonoidHom) := by
  simp only [inflate, MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]
end OAI.SevenEighths.ResidueCharacter
