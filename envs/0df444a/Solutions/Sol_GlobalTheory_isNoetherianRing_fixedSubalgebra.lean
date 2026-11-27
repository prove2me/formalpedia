-- Prove2me | solution 1 for GlobalTheory.isNoetherianRing_fixedSubalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:35.834923+00:00
-- url     : https://prove2.me/submissions/f333033c-b65b-4f7f-9862-e83b78373fe7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_finiteType_fixedSubalgebra

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
    IsNoetherianRing (FixedPoints.subalgebra R A G) :=
  haveI := finiteType_fixedSubalgebra A G R
  Algebra.FiniteType.isNoetherianRing R _
end GlobalTheory
