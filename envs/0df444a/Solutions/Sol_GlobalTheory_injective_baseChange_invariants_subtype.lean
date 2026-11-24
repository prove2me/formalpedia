-- Prove2me | solution 1 for GlobalTheory.injective_baseChange_invariants_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:00:19.323414+00:00
-- url     : https://prove2.me/submissions/5a3ddd63-edbd-4e49-975b-d14550d04090

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
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']
variable {G : Type*} [Group G]
namespace GlobalTheory
theorem _root_.solution [Module.Flat R S] (ρ : Representation R G M) :
    Function.Injective (ρ.invariants.subtype.baseChange S) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
end GlobalTheory
