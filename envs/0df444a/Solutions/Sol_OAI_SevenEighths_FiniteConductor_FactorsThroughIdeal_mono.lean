-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:18.99091+00:00
-- url     : https://prove2.me/submissions/17183e5b-e037-4466-9d1f-6426c0d86b4a

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
namespace FactorsThroughIdeal
theorem _root_.solution {χ : MulChar R ℂ} {I J : Ideal R}
    (h : FactorsThroughIdeal χ I) (hJI : J ≤ I) : FactorsThroughIdeal χ J := by
  rw [factorsThroughIdeal_iff] at h ⊢
  exact fun u hu => h u (hJI hu)
end FactorsThroughIdeal
end OAI.SevenEighths.FiniteConductor
