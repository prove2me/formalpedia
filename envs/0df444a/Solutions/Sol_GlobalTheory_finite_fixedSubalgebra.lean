-- Prove2me | solution 1 for GlobalTheory.finite_fixedSubalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:00.526993+00:00
-- url     : https://prove2.me/submissions/661e7e2e-b9a6-49f3-a761-7e553419641e

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
theorem _root_.solution [Finite G] (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] [Algebra.FiniteType R A] :
    Module.Finite (FixedPoints.subalgebra R A G) A :=
  finite_of_isInvariant A G R _
end GlobalTheory
