-- Prove2me | solution 1 for GlobalTheory.finiteType_of_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:13.868627+00:00
-- url     : https://prove2.me/submissions/f4bb3def-494c-4d4f-9264-9f94c9ac231c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_finite_of_isInvariant

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
    [Algebra R B] [Algebra B A] [IsScalarTower R B A] [FaithfulSMul B A]
    [Algebra.IsInvariant B A G] [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FiniteType R B :=
  haveI := finite_of_isInvariant A G R B
  ⟨fg_of_fg_of_fg R B A Algebra.FiniteType.out Module.Finite.fg_top
    (FaithfulSMul.algebraMap_injective B A)⟩
end GlobalTheory
