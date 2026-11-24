-- Prove2me | solution 1 for GlobalTheory.LocalFlatMax.flat_of_lTensor_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:23:00.931113+00:00
-- url     : https://prove2.me/submissions/9b8b6961-51f0-4850-a2ed-a0a8a5ca32da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomFlatOfCompFlatOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_LocalFlatMax_lTensor_injective_of_pow_smul_le
import Theorems.Thm_GlobalTheory_LocalFlatMax_relationsLift_of_lTensor_injective
import Theorems.Thm_GlobalTheory_LocalFlat_flat_of_relationsLift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap IsLocalRing
open GlobalTheory
open GlobalTheory.LocalFlatMax
universe u
variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
namespace GlobalTheory.LocalFlatMax
theorem _root_.solution [IsNoetherianRing A] (B : Type*) [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] (I : Ideal A)
    [I.IsMaximal] (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M :=
  LocalFlat.flat_of_relationsLift B hI fun n =>
    relationsLift_of_lTensor_injective _ fun L hL =>
      lTensor_injective_of_pow_smul_le I h n L (by simpa using hL)
end GlobalTheory.LocalFlatMax
