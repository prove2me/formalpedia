-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:19.67682+00:00
-- url     : https://prove2.me/submissions/e348c076-f3a3-48b5-8529-886b07500db2

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
theorem _root_.solution {χ : MulChar R ℂ} {I : Ideal R}
    (h : FactorsThroughIdeal χ I) : FactorsThroughIdeal χ⁻¹ I := by
  rw [factorsThroughIdeal_iff] at h ⊢
  intro u hu
  rw [← MulChar.star_apply', h u hu, star_one]
end FactorsThroughIdeal
end OAI.SevenEighths.FiniteConductor
