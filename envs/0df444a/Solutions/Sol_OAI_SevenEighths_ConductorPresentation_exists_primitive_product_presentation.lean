-- Prove2me | solution 1 for OAI.SevenEighths.ConductorPresentation.exists_primitive_product_presentation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:45.329204+00:00
-- url     : https://prove2.me/submissions/dd588ff5-8912-44ca-863f-558a760e3cb4

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_primitive_quotientCharacter
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_source_le_comap
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_comap_ne_bot
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_exists_primitive_residue_product_with_norm_and_mask
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
    (M L₁ L₂ : Ideal A) [Finite (A ⧸ M)] (hML₁ : M ≤ L₁) (hML₂ : M ≤ L₂)
    (χ ψ : MulChar (A ⧸ M) ℂ)
    (hχ : FactorsThroughIdeal χ (L₁.map (Ideal.Quotient.mk M)))
    (hψ : FactorsThroughIdeal ψ (L₂.map (Ideal.Quotient.mk M))) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ L₁ ⊓ L₂ ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.cardQuot ≤ L₁.cardQuot * L₂.cardQuot ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) * ψ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal, hnorm, hmask⟩ :=
    exists_primitive_residue_product_with_norm_and_mask M χ ψ
      (L₁.map (Ideal.Quotient.mk M)) (L₂.map (Ideal.Quotient.mk M)) hχ hψ
  refine ⟨I.comap (Ideal.Quotient.mk M), quotientCharacter M I φ,
    source_le_comap M I, ?_, comap_ne_bot M I,
    primitive_quotientCharacter M I φ hprimitive, ?_, ?_⟩
  · have h := Ideal.comap_mono (f := Ideal.Quotient.mk M) hJI
    simpa only [Ideal.comap_inf, Ideal.comap_map_mk hML₁, Ideal.comap_map_mk hML₂] using h
  · simpa only [Ideal.comap_map_mk hML₁, Ideal.comap_map_mk hML₂] using hnorm
  · intro a
    simpa only [quotientCharacter_mk] using hmask (Ideal.Quotient.mk M a)
end OAI.SevenEighths.ConductorPresentation
