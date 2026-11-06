-- Prove2me | solution 1 for OAI.SevenEighths.ResidueCharacter.exists_primitive_product_global_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:54.313879+00:00
-- url     : https://prove2.me/submissions/b4d0b3ca-246e-40db-b998-3040a6ec4c91

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_exists_primitive_product
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
variable [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
namespace OAI.SevenEighths.ResidueCharacter
theorem _root_.solution
    (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)]
    (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ)
    (hχ : ∀ u : Aˣ, χ (Ideal.Quotient.mk I u) = 1)
    (hψ : ∀ u : Aˣ, ψ (Ideal.Quotient.mk J u) = 1) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.cardQuot ≤ I.cardQuot * J.cardQuot ∧
      (∀ u : Aˣ, φ (Ideal.Quotient.mk K u) = 1) ∧
      ∀ a : A, χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) =
        if IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a)
          then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hIK, hK, hprimitive, hnorm, hmask⟩ := exists_primitive_product I J χ ψ
  refine ⟨K, φ, hIK, hK, hprimitive, hnorm, ?_, hmask⟩
  intro u
  have h := hmask (u : A)
  simpa only [hχ, hψ, one_mul, u.isUnit.map (Ideal.Quotient.mk I),
    u.isUnit.map (Ideal.Quotient.mk J), and_self, ite_true] using h.symm
end OAI.SevenEighths.ResidueCharacter
