-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.exists_primitive_quotient_above_with_bound_and_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:47:21.958216+00:00
-- url     : https://prove2.me/submissions/3e027b5a-4a82-4999-ae08-86fd61ef0652

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_quotient_card_le_of_le
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_exists_primitive_quotient_above
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_factorization_with_source_mask


set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution
    (χ : MulChar R ℂ) (J : Ideal R) (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      Nat.card (R ⧸ I) ≤ Nat.card (R ⧸ J) ∧
      ∀ a : R, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  let : Finite (R ⧸ J) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal⟩ := exists_primitive_quotient_above χ J hJ
  exact ⟨I, φ, hJI, hφ, hprimitive, hmaximal, quotient_card_le_of_le hJI,
    factorization_with_source_mask χ I φ hφ⟩
end OAI.SevenEighths.FiniteConductor
