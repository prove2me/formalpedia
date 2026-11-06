-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.exists_primitive_residue_product_with_norm_and_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:49:16.935473+00:00
-- url     : https://prove2.me/submissions/a5c90efa-2655-4766-abc1-de88f69dcf12

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_exists_primitive_product_quotient_with_bound_and_mask
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_absNorm_comap_eq_quotient_card

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution
    (M : Ideal A) [Finite (A ⧸ M)] (χ ψ : MulChar (A ⧸ M) ℂ)
    (I J : Ideal (A ⧸ M))
    (hχ : FactorsThroughIdeal χ I) (hψ : FactorsThroughIdeal ψ J) :
    ∃ (K : Ideal (A ⧸ M)) (φ : MulChar ((A ⧸ M) ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ φ.toUnitHom.comp (quotientUnits K) = (χ * ψ).toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal (χ * ψ)) K ∧
      (K.comap (Ideal.Quotient.mk M)).cardQuot ≤
        (I.comap (Ideal.Quotient.mk M)).cardQuot *
          (J.comap (Ideal.Quotient.mk M)).cardQuot ∧
      ∀ a : A ⧸ M, χ a * ψ a = if IsUnit a then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hIK, hφ, hprimitive, hmaximal, hcard, hmask⟩ :=
    exists_primitive_product_quotient_with_bound_and_mask χ ψ I J hχ hψ
  refine ⟨K, φ, hIK, hφ, hprimitive, hmaximal, ?_, hmask⟩
  simpa only [absNorm_comap_eq_quotient_card] using hcard
end OAI.SevenEighths.FiniteConductor
