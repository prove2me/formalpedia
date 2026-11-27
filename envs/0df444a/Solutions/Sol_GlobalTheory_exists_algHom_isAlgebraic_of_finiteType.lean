-- Prove2me | solution 1 for GlobalTheory.exists_algHom_isAlgebraic_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:10.993403+00:00
-- url     : https://prove2.me/submissions/d40aa169-ffac-4f62-9197-a29838695987

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
theorem _root_.solution (F A L : Type*) [Field F] [CommRing A]
    [Nontrivial A] [Algebra F A] [Algebra.FiniteType F A] [Field L] [IsAlgClosed L] [Algebra F L] :
    ∃ φ : A →ₐ[F] L, ∀ x, IsAlgebraic F (φ x) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  refine ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] L).comp (Ideal.Quotient.mkₐ F m), fun x => ?_⟩
  exact (Algebra.IsAlgebraic.isAlgebraic (R := F) (Ideal.Quotient.mkₐ F m x)).algHom
    (IsAlgClosed.lift : (A ⧸ m) →ₐ[F] L)
end GlobalTheory
