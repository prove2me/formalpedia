-- Prove2me | solution 1 for GlobalTheory.NormVal.isLocalHom_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:02:20.421446+00:00
-- url     : https://prove2.me/submissions/32b0a518-89fd-427a-8b93-31141d4eb226

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_liesOver_maximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]
namespace GlobalTheory.NormVal
theorem _root_.solution (n : Ideal S) [n.IsMaximal] (B : Type*) [CommRing B] [IsLocalRing B]
    [Algebra S B] [IsLocalization.AtPrime B n] [Algebra R B] [IsScalarTower R S B] :
    IsLocalHom (algebraMap R B) := by
  have := liesOver_maximalIdeal R n
  refine ⟨fun a ha => ?_⟩
  rw [IsScalarTower.algebraMap_apply R S B, IsLocalization.AtPrime.isUnit_to_map_iff B n] at ha
  by_contra hu
  exact ha ((Ideal.mem_of_liesOver n (maximalIdeal R) a).1 hu)
end GlobalTheory.NormVal
