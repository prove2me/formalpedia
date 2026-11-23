-- Prove2me | solution 1 for GlobalTheory.isIntegral_fixedSubring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:35.664438+00:00
-- url     : https://prove2.me/submissions/5db9d6ee-e360-4748-ab01-59730b7e65e2

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
theorem _root_.solution [Finite G] : Algebra.IsIntegral (FixedPoints.subring A G) A :=
  Algebra.IsInvariant.isIntegral _ A G
end GlobalTheory
