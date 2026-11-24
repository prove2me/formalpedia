-- Prove2me | solution 1 for GlobalTheory.SemilinearModule.invariantsFunctor_isEquivalence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:53.361982+00:00
-- url     : https://prove2.me/submissions/f77fa721-cca0-4702-be90-90e763e450ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_SemilinearModule_invariantsFunctor_faithful
import Theorems.Thm_GlobalTheory_SemilinearModule_invariantsFunctor_full
import Theorems.Thm_GlobalTheory_SemilinearModule_invariantsFunctor_essSurj

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
    (invariantsFunctor.{max w u} G A).IsEquivalence where
  faithful := invariantsFunctor_faithful h
  full := invariantsFunctor_full h
  essSurj := invariantsFunctor_essSurj.{w} h
end GlobalTheory.SemilinearModule
