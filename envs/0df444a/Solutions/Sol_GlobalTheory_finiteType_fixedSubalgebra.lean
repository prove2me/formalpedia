-- Prove2me | solution 1 for GlobalTheory.finiteType_fixedSubalgebra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:22.285272+00:00
-- url     : https://prove2.me/submissions/a3695a5c-7b35-459f-87b5-e73924ee420f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_finiteType_of_isInvariant

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
    [SMulCommClass G R A] [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FiniteType R (FixedPoints.subalgebra R A G) :=
  finiteType_of_isInvariant A G R _
end GlobalTheory
