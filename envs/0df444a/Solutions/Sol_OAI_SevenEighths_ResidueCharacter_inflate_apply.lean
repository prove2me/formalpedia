-- Prove2me | solution 1 for OAI.SevenEighths.ResidueCharacter.inflate_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:43:30.275193+00:00
-- url     : https://prove2.me/submissions/be7cf53e-20a4-4a51-ac4e-bcc34bacfa52

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_inflate_apply_unit
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
theorem _root_.solution {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (x : A ⧸ M) :
    inflate hML χ x = if IsUnit x then χ (Ideal.Quotient.factor hML x) else 0 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simpa only [u.isUnit, ite_true] using inflate_apply_unit hML χ u
  · simp only [hx, ite_false, MulChar.map_nonunit _ hx]
end OAI.SevenEighths.ResidueCharacter
