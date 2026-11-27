-- Prove2me | solution 1 for GlobalTheory.flat_of_flat_quotientMap_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:37.479161+00:00
-- url     : https://prove2.me/submissions/b31757d6-b275-4dad-852a-802fe7025ed0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_flat_of_flat_reduction_dvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra T A] [Algebra T B] [IsLocalRing B] [IsLocalHom (algebraMap T B)] [Module.Flat T B]
namespace GlobalTheory
theorem _root_.solution (φ : A →ₐ[T] B)
    (hle : (maximalIdeal T).map (algebraMap T A) ≤
      ((maximalIdeal T).map (algebraMap T B)).comap (φ : A →+* B))
    (h : (Ideal.quotientMap _ (φ : A →+* B) hle).Flat) : (φ : A →+* B).Flat :=
  flat_of_flat_reduction_dvr φ (Ideal.Quotient.mk _) (Ideal.Quotient.mk _) _
    Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective Ideal.mk_ker Ideal.mk_ker
    (Ideal.quotientMap_comp_mk hle) h
end GlobalTheory
