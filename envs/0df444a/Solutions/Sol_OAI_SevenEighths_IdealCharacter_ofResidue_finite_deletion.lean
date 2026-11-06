-- Prove2me | solution 1 for OAI.SevenEighths.IdealCharacter.ofResidue_finite_deletion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:00:41.609109+00:00
-- url     : https://prove2.me/submissions/383650d1-da9f-4b10-8179-ea40332ed10c

import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_bot
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_one
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_source_mask
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
theorem _root_.solution (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I =
      ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  rw [ofResidue_source_mask M K χ φ hχ hφ hmask, ofResidue_one]
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true, ite_self, mul_zero]
  · simp only [hI, ite_false]
    split_ifs <;> simp only [one_mul, zero_mul]
end OAI.SevenEighths.IdealCharacter
