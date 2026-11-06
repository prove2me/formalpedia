-- Prove2me | solution 1 for OAI.SevenEighths.ResidueCharacter.exists_primitive_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:51:22.71562+00:00
-- url     : https://prove2.me/submissions/1b2f9627-e7e2-4d9c-b32f-5f909d69a6fb

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_isUnit_mk_inf_iff
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_finite_quotient_inf
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_product_mk
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_exists_primitive_presentation
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_absNorm_inf_le_mul
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
variable [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
namespace OAI.SevenEighths.ResidueCharacter
theorem _root_.solution (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)]
    (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.cardQuot ≤ I.cardQuot * J.cardQuot ∧
      ∀ a : A, χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) =
        if IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a)
          then φ (Ideal.Quotient.mk K a) else 0 := by
  let : Finite (A ⧸ I ⊓ J) := finite_quotient_inf I J
  obtain ⟨K, φ, hIK, hK, hprimitive, hnorm, hmask⟩ :=
    exists_primitive_presentation (I ⊓ J) (product I J χ ψ)
  refine ⟨K, φ, hIK, hK, hprimitive, hnorm.trans (absNorm_inf_le_mul I J), ?_⟩
  intro a
  simpa only [product_mk, isUnit_mk_inf_iff] using hmask a
end OAI.SevenEighths.ResidueCharacter
