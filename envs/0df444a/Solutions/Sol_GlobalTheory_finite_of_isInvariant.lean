-- Prove2me | solution 1 for GlobalTheory.finite_of_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:40.596047+00:00
-- url     : https://prove2.me/submissions/00f404d0-b6ff-4878-8ddd-a92b3c4b78a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]
namespace GlobalTheory
theorem _root_.solution [Finite G] (R B : Type*) [CommRing R] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra B A] [IsScalarTower R B A] [Algebra.IsInvariant B A G]
    [Algebra.FiniteType R A] : Module.Finite B A := by
  haveI := Algebra.IsInvariant.isIntegral B A G
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType R B A
  exact Algebra.IsIntegral.finite
end GlobalTheory
