-- Prove2me | solution 1 for GlobalTheory.SemilinearModule.invariantsFunctor_faithful
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:43:00.591802+00:00
-- url     : https://prove2.me/submissions/88c28e74-908a-41f3-a7a3-42280b7acfdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_isBaseChange_invariants
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor

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
    (invariantsFunctor.{w} G A).Faithful where
  map_injective {M N} f f' hff' := Subtype.ext <|
    (FreeQuotient.isBaseChange_invariants (FixedPoints.subring A G) M.carrier h).algHom_ext _ _
      fun x ↦ congrArg Subtype.val (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hff') x)
end GlobalTheory.SemilinearModule
