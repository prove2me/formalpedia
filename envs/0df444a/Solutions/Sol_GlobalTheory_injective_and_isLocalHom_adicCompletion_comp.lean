-- Prove2me | solution 1 for GlobalTheory.injective_and_isLocalHom_adicCompletion_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:24.429969+00:00
-- url     : https://prove2.me/submissions/6abf06ca-cae7-4a58-bcc4-77ff9793022b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S] {V : Type*}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : S →+* V)
    (hf : Function.Injective f) [IsLocalHom f] :
    Function.Injective ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp f) ∧
      IsLocalHom ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp f) :=
  ⟨(algebraMap_adicCompletion_injective_of_dvr V).comp hf, RingHom.isLocalHom_comp _ _⟩
end GlobalTheory
