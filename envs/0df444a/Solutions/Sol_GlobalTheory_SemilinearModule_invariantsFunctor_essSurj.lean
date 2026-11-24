-- Prove2me | solution 1 for GlobalTheory.SemilinearModule.invariantsFunctor_essSurj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:42:59.147969+00:00
-- url     : https://prove2.me/submissions/2346b299-441e-4fd7-a847-fa8b7b2fe516

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_bijective_toInvariantsTensor

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
universe w v u
open CategoryTheory
open GlobalTheory.SemilinearModule
attribute [instance] addCommGroup module action semilinear
variable (G : Type v) [Group G] (A : Type u) [CommRing A] [MulSemiringAction G A]
variable {G A}
namespace GlobalTheory.SemilinearModule
theorem _root_.solution [Finite G] (h : IsFreeRingAction G A) :
    (invariantsFunctor.{max w u} G A).EssSurj where
  mem_essImage N := ⟨baseChange.{max w u} G A N, ⟨(LinearEquiv.ofBijective _
    (FreeQuotient.bijective_toInvariantsTensor (FixedPoints.subring A G) N h)).symm.toModuleIso⟩⟩
end GlobalTheory.SemilinearModule
