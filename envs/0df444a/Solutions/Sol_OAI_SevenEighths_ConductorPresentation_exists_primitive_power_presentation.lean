-- Prove2me | solution 1 for OAI.SevenEighths.ConductorPresentation.exists_primitive_power_presentation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:45.93425+00:00
-- url     : https://prove2.me/submissions/fe724240-61fa-4f97-8c32-d9e57c0d9b50

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_FactorsThroughIdeal_pow
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_exists_primitive_presentation_above

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
    (hχ : FactorsThroughIdeal χ (L.map (Ideal.Quotient.mk M))) (n : ℕ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ L ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.cardQuot ≤ L.cardQuot ∧
      ∀ a : A, (χ ^ n) (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 :=
  exists_primitive_presentation_above M L hML (χ ^ n) (hχ.pow n)
end OAI.SevenEighths.ConductorPresentation
