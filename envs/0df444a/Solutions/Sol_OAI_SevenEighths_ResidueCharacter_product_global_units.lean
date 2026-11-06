-- Prove2me | solution 1 for OAI.SevenEighths.ResidueCharacter.product_global_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:46:12.318192+00:00
-- url     : https://prove2.me/submissions/1692e6a7-dccb-4c85-868b-f08d9387090d

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_product_mk

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ResidueCharacter
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]
namespace OAI.SevenEighths.ResidueCharacter
theorem _root_.solution (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ)
    (ψ : MulChar (A ⧸ J) ℂ)
    (hχ : ∀ u : Aˣ, χ (Ideal.Quotient.mk I u) = 1)
    (hψ : ∀ u : Aˣ, ψ (Ideal.Quotient.mk J u) = 1) :
    ∀ u : Aˣ, product I J χ ψ (Ideal.Quotient.mk (I ⊓ J) u) = 1 := by
  intro u
  rw [product_mk, hχ, hψ, one_mul]
end OAI.SevenEighths.ResidueCharacter
