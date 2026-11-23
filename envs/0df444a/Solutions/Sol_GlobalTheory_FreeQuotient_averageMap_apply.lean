-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.averageMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:59.716262+00:00
-- url     : https://prove2.me/submissions/3fbfe03b-ffed-4fdc-84ea-c6f2ce2afc3e

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
variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution (f : M →ₗ[A] N) (m : M) :
    averageMap G f m = ∑ g : G, g • f (g⁻¹ • m) := rfl
end GlobalTheory.FreeQuotient
