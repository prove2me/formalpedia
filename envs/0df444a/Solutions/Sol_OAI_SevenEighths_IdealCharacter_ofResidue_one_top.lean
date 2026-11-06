-- Prove2me | solution 1 for OAI.SevenEighths.IdealCharacter.ofResidue_one_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:00:42.154986+00:00
-- url     : https://prove2.me/submissions/dce18b6b-d8d3-4427-93ea-efc3536ab6fe

import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_bot
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_one
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
theorem _root_.solution (I : Ideal A) :
    ofResidue (⊤ : Ideal A) 1 (one_unitInvariant ⊤) I = if I = ⊥ then 0 else 1 := by
  rw [ofResidue_one]
  have h : IsCoprime I (⊤ : Ideal A) := Ideal.isCoprime_iff_sup_eq.mpr (sup_top_eq I)
  simp only [h, ite_true]
end OAI.SevenEighths.IdealCharacter
