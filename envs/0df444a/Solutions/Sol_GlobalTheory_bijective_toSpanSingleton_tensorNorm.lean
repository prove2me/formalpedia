-- Prove2me | solution 1 for GlobalTheory.bijective_toSpanSingleton_tensorNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:34:48.333544+00:00
-- url     : https://prove2.me/submissions/18b372a2-ba0e-4dc8-85b7-6ba8c278d3f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_bijective_toSpanSingleton_tprod
import Theorems.Thm_GlobalTheory_bijective_toSpanSingleton_smul

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
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] {ι : Type*}
variable [SMulDistribClass G A M]
variable {A}
namespace GlobalTheory
theorem _root_.solution [Finite G] (κ : ι ≃ G) {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) :
    Function.Bijective (LinearMap.toSpanSingleton A _ (tensorNorm A κ e)) :=
  haveI : Finite ι := .of_equiv _ κ.symm
  bijective_toSpanSingleton_tprod _ fun i ↦ bijective_toSpanSingleton_smul he (κ i)
end GlobalTheory
