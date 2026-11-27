-- Prove2me | solution 2 for GlobalTheory.mem_fixedSubalgebra_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:41.896674+00:00
-- url     : https://prove2.me/submissions/dcb6e87c-e85e-4f1d-b8ce-dafe7459ab21

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
theorem _root_.solution (R : Type*) [CommRing R] [Algebra R A] [SMulCommClass G R A]
    {a : A} : a ∈ FixedPoints.subalgebra R A G ↔ ∀ g : G, g • a = a :=
  Iff.rfl
end GlobalTheory
