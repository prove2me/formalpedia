-- Prove2me | solution 1 for GlobalTheory.isIntegral_fixedSubalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:51.455216+00:00
-- url     : https://prove2.me/submissions/682a805b-d1f4-47e3-b201-44232c71ba04

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
theorem _root_.solution [Finite G] (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] : Algebra.IsIntegral (FixedPoints.subalgebra R A G) A :=
  Algebra.IsInvariant.isIntegral _ A G
end GlobalTheory
