-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.exists_primitive_quotient_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:46:19.803319+00:00
-- url     : https://prove2.me/submissions/57300177-48ff-48c2-bc23-489beadf215f

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_primitive_of_maximal_descent

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (χ : MulChar R ℂ) (J : Ideal R)
    (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I := by
  let : Finite (Ideal R) := Finite.of_injective
    (fun I : Ideal R => (I : Set R)) SetLike.coe_injective
  obtain ⟨I, hJI, hI⟩ := Finite.exists_le_maximal hJ
  obtain ⟨φ, hφ⟩ := hI.1
  exact ⟨I, φ, hJI, hφ, primitive_of_maximal_descent χ I φ hφ hI, hI⟩
end OAI.SevenEighths.FiniteConductor
