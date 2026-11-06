-- Prove2me | solution 1 for OAI.SevenEighths.ConductorPresentation.exists_primitive_presentation_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:50:34.667936+00:00
-- url     : https://prove2.me/submissions/60043911-c9be-425a-bc31-4097584de6fc

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_exists_primitive_presentation_above_quotient
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_apply
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_mul
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_symm


attribute [local simp] OAI.SevenEighths.ConductorPresentation.quotientCharacter_mk

set_option autoImplicit false
open OAI
open OAI.SevenEighths
open OAI.SevenEighths.ConductorPresentation
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
namespace OAI.SevenEighths.ConductorPresentation
theorem _root_.solution
    (M L : Ideal A) [Finite (A ⧸ M)] (hML : M ≤ L)
    (χ : MulChar (A ⧸ M) ℂ)
    (hL : FactorsThroughIdeal χ (L.map (Ideal.Quotient.mk M))) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ L ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.cardQuot ≤ L.cardQuot ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  simpa only [Ideal.comap_map_mk hML] using
    exists_primitive_presentation_above_quotient M χ (L.map (Ideal.Quotient.mk M)) hL
end OAI.SevenEighths.ConductorPresentation
