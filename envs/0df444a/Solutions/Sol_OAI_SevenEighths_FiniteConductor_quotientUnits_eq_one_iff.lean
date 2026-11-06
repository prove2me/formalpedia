-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.quotientUnits_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:56.5746+00:00
-- url     : https://prove2.me/submissions/2d9bf513-58bd-4879-b0a8-43b47a4c8930

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]
omit [Finite R]
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (I : Ideal R) (u : Rˣ) :
    quotientUnits I u = 1 ↔ (u : R) - 1 ∈ I := by
  rw [← Units.val_inj]
  exact Ideal.Quotient.mk_eq_one_iff_sub_mem _
end OAI.SevenEighths.FiniteConductor
