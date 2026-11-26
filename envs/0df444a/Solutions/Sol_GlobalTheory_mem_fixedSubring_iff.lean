-- Prove2me | solution 1 for GlobalTheory.mem_fixedSubring_iff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:10:26.281459+00:00
-- url     : https://prove2.me/submissions/4f1f95e0-3b1e-42c2-85ca-e29da006424d

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
theorem _root_.solution {a : A} : a ∈ FixedPoints.subring A G ↔ ∀ g : G, g • a = a := by
  exact Iff.rfl

