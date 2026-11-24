-- Prove2me | solution 1 for GlobalTheory.ker_includeRight_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:18.163451+00:00
-- url     : https://prove2.me/submissions/ae89b5fa-2f49-4cb1-9efd-9ab0e7a19997

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal

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
theorem _root_.solution {T : Type*} (A : Type*) [CommRing T] [CommRing A] [Algebra T A]
    (I : Ideal T) :
    RingHom.ker ((Algebra.TensorProduct.includeRight : A →ₐ[T] (T ⧸ I) ⊗[T] A) :
      A →+* (T ⧸ I) ⊗[T] A) = I.map (algebraMap T A) := by
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem,
    ← map_eq_zero_iff _ (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).injective,
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  rfl
end GlobalTheory
