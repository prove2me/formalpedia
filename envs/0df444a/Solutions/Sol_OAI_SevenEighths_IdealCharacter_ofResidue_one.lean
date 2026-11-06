-- Prove2me | solution 1 for OAI.SevenEighths.IdealCharacter.ofResidue_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T04:59:41.745016+00:00
-- url     : https://prove2.me/submissions/4411a9b0-9d77-4313-b338-9ab854f82181

import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_isUnit_mk_iff_isCoprime
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_bot
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_span
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
theorem _root_.solution (M : Ideal A) (I : Ideal A) :
    ofResidue M 1 (one_unitInvariant M) I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have heq := ofResidue_span M 1 (one_unitInvariant M) hg
    rw [Ideal.span_singleton_generator] at heq
    rw [heq]
    simp only [hI, ite_false]
    have hu : IsUnit (Ideal.Quotient.mk M (generator I)) ↔ IsCoprime I M := by
      simpa only [Ideal.span_singleton_generator] using isUnit_mk_iff_isCoprime M (generator I)
    by_cases hc : IsCoprime I M
    · simp only [hc, ite_true]
      exact MulChar.one_apply (hu.mpr hc)
    · simp only [hc, ite_false]
      exact MulChar.map_nonunit _ (fun h => hc (hu.mp h))
end OAI.SevenEighths.IdealCharacter
