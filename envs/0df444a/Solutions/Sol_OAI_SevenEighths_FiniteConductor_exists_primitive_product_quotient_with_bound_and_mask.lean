-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.exists_primitive_product_quotient_with_bound_and_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:48:26.357198+00:00
-- url     : https://prove2.me/submissions/89bfd7e9-b48e-4f44-87b8-dc2826d69380

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_quotient_inf_card_le_mul
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_exists_primitive_quotient_above_with_bound_and_mask
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_FactorsThroughIdeal_mul

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution
    (χ ψ : MulChar R ℂ) (I J : Ideal R)
    (hχ : FactorsThroughIdeal χ I) (hψ : FactorsThroughIdeal ψ J) :
    ∃ (K : Ideal R) (φ : MulChar (R ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ φ.toUnitHom.comp (quotientUnits K) = (χ * ψ).toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal (χ * ψ)) K ∧
      Nat.card (R ⧸ K) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) ∧
      ∀ a : R, χ a * ψ a = if IsUnit a then φ (Ideal.Quotient.mk K a) else 0 := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  let : Finite (R ⧸ J) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))
  obtain ⟨K, φ, hIK, hφ, hprimitive, hmaximal, hcard, hmask⟩ :=
    exists_primitive_quotient_above_with_bound_and_mask (χ * ψ) (I ⊓ J) (hχ.mul hψ)
  exact ⟨K, φ, hIK, hφ, hprimitive, hmaximal,
    hcard.trans (quotient_inf_card_le_mul I J), hmask⟩
end OAI.SevenEighths.FiniteConductor
