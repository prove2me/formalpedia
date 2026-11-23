-- Prove2me | solution 1 for GlobalTheory.exists_ringHom_extend_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:31.241159+00:00
-- url     : https://prove2.me/submissions/d0f566fa-85b9-4a39-ab3c-9d74df7f2063

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (F A L : Type*) [Field F] [CommRing A]
    [Nontrivial A] [Algebra F A] [Algebra.FiniteType F A] [Field L] [IsAlgClosed L]
    (σ : F →+* L) : ∃ φ : A →+* L, ∀ x, φ (algebraMap F A x) = σ x := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  letI : Algebra F L := σ.toAlgebra
  let ψ : (A ⧸ m) →ₐ[F] L := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), fun x => ?_⟩
  have h1 : Ideal.Quotient.mk m (algebraMap F A x) = algebraMap F (A ⧸ m) x := rfl
  simp only [RingHom.comp_apply, h1, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl
end _root_.GlobalTheory
end GlobalTheory
