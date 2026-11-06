-- Prove2me | solution 1 for OAI.SevenEighths.ResidueCharacter.product_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:45:11.265203+00:00
-- url     : https://prove2.me/submissions/f82bd2db-c1ee-4275-90be-53f725bf4a38

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_inflate_mk
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_isUnit_mk_inf_iff
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
theorem _root_.solution (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ)
    (a : A) :
    product I J χ ψ (Ideal.Quotient.mk (I ⊓ J) a) =
      χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) := by
  rw [product, MulChar.mul_apply, inflate_mk, inflate_mk]
  by_cases ha : IsUnit (Ideal.Quotient.mk (I ⊓ J) a)
  · simp only [ha, ite_true]
  · simp only [ha, ite_false, zero_mul]
    by_cases hI : IsUnit (Ideal.Quotient.mk I a)
    · have hJ : ¬ IsUnit (Ideal.Quotient.mk J a) := fun hJ =>
        ha ((isUnit_mk_inf_iff I J a).mpr ⟨hI, hJ⟩)
      rw [MulChar.map_nonunit _ hJ, mul_zero]
    · rw [MulChar.map_nonunit _ hI, zero_mul]
end OAI.SevenEighths.ResidueCharacter
