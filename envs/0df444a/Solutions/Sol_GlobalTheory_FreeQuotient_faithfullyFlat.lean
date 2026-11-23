-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:41.514447+00:00
-- url     : https://prove2.me/submissions/fd4bd9e5-9b3d-4ce8-ae9e-f373c63774a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_finite_and_projective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.FreeQuotient
variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]
variable [Finite G] (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution (h : IsFreeRingAction G A) : Module.FaithfullyFlat B A :=
  haveI := (finite_and_projective B h).1
  haveI := (finite_and_projective B h).2
  .of_comap_surjective (Algebra.IsIntegral.comap_surjective B A)
end GlobalTheory.FreeQuotient
