-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.exists_primitive_quotient_with_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:22.933052+00:00
-- url     : https://prove2.me/submissions/f21e8c3b-4866-4ffc-9821-50ff6e1305e5

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_factorization_with_source_mask
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_exists_primitive_quotient

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (χ : MulChar R ℂ) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      ∀ a : R, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  obtain ⟨I, φ, hφ, hprimitive, hmaximal⟩ := exists_primitive_quotient χ
  exact ⟨I, φ, hprimitive, hmaximal, factorization_with_source_mask χ I φ hφ⟩
end OAI.SevenEighths.FiniteConductor
