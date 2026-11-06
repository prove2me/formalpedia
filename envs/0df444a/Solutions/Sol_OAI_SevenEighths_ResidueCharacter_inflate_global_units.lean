-- Prove2me | solution 1 for OAI.SevenEighths.ResidueCharacter.inflate_global_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:53.701762+00:00
-- url     : https://prove2.me/submissions/debe4ee5-dc83-4eb7-bd4b-cdd437d94997

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_inflate_mk
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
    (hχ : ∀ u : Aˣ, χ (Ideal.Quotient.mk L u) = 1) :
    ∀ u : Aˣ, inflate hML χ (Ideal.Quotient.mk M u) = 1 := by
  intro u
  rw [inflate_mk]
  simp only [u.isUnit.map (Ideal.Quotient.mk M), ite_true, hχ]
end OAI.SevenEighths.ResidueCharacter
