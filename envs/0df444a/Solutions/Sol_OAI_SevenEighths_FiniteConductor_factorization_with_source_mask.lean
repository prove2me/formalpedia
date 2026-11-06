-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.factorization_with_source_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:13:18.47321+00:00
-- url     : https://prove2.me/submissions/8b658786-1fe2-40c3-8313-7ec4873403af

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
theorem _root_.solution (χ : MulChar R ℂ) (I : Ideal R)
    (φ : MulChar (R ⧸ I) ℂ)
    (hφ : φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom) (a : R) :
    χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  classical
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    simp only [u.isUnit, ite_true]
    exact (congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ).symm
  · simp only [ha, ite_false, MulChar.map_nonunit _ ha]
end OAI.SevenEighths.FiniteConductor
