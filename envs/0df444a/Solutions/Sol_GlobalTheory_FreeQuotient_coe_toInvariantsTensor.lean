-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.coe_toInvariantsTensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:46.669273+00:00
-- url     : https://prove2.me/submissions/47fb8d38-fd87-4556-a89e-d2fc657a7129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime

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
variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass B G A]
  (N : Type*) [AddCommGroup N] [Module B N]
variable [SMulCommClass G B A]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution (n : N) :
    (toInvariantsTensor G A B N n : A ⊗[B] N) = 1 ⊗ₜ n := rfl
end GlobalTheory.FreeQuotient
