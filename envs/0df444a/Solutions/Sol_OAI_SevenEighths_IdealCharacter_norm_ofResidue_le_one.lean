-- Prove2me | solution 1 for OAI.SevenEighths.IdealCharacter.norm_ofResidue_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:01:03.077123+00:00
-- url     : https://prove2.me/submissions/8c8a4bb8-35c1-463c-9944-49b290805786

import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_bot
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_norm_residue_le_one
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_apply
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_mul
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_symm
attribute [local simp] OAI.SevenEighths.ConductorPresentation.quotientCharacter_mk


attribute [local simp] OAI.SevenEighths.IdealCharacter.ofResidue_bot

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.IdealCharacter
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]
variable [IsDomain A] [IsPrincipalIdealRing A]
namespace OAI.SevenEighths.IdealCharacter
theorem _root_.solution (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) (I : Ideal A) :
    ‖ofResidue M χ hχ I‖ ≤ 1 := by
  by_cases hI : I = ⊥
  · rw [hI, ofResidue_bot, norm_zero]
    exact zero_le_one
  · change ‖value M χ I‖ ≤ 1
    simp only [value, hI, ite_false]
    exact norm_residue_le_one M χ _
end OAI.SevenEighths.IdealCharacter
