-- Prove2me | solution 1 for GlobalTheory.algebraMap_trace_eq_sum_of_equiv_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:03:52.623391+00:00
-- url     : https://prove2.me/submissions/149bc641-bae3-4d03-97c4-0b26e93d91e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_algebraMap_trace_eq_sum_algHom_of_card
import Theorems.Thm_GlobalTheory_card_eq_finrank_of_equiv_algHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable (K : Type*) {S : Type*} (L : Type*) [Field K] [CommRing S] [Algebra K S] [Field L]
  [Algebra K L] [IsSepClosed L] [Algebra.Etale K S]
variable {K L} {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (P : ι ≃ (S →ₐ[K] L)) (x : S) :
    algebraMap K L (Algebra.trace K S x) = ∑ j, P j x :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  algebraMap_trace_eq_sum_algHom_of_card (card_eq_finrank_of_equiv_algHom P) P.injective x
end GlobalTheory
