-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.primitiveOnIdeals_iff_no_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:39.057198+00:00
-- url     : https://prove2.me/submissions/0430c7bd-2da6-486f-88d3-03ba955e4285

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_factorsThroughIdeal_iff

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (χ : MulChar R ℂ) :
    IsPrimitiveOnIdeals χ ↔ ∀ I : Ideal R, I ≠ ⊥ → ¬ FactorsThroughIdeal χ I := by
  simp only [IsPrimitiveOnIdeals, factorsThroughIdeal_iff]
  push Not
  rfl
end OAI.SevenEighths.FiniteConductor
