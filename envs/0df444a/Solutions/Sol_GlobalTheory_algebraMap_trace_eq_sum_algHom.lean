-- Prove2me | solution 1 for GlobalTheory.algebraMap_trace_eq_sum_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:03.725807+00:00
-- url     : https://prove2.me/submissions/014e90b5-d2b0-46f3-acb8-9dfb8b5058a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_algebraMap_trace_eq_sum_algHom_of_card

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
namespace GlobalTheory
theorem _root_.solution [Fintype (S →ₐ[K] L)] (x : S) :
    algebraMap K L (Algebra.trace K S x) = ∑ P : S →ₐ[K] L, P x :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  algebraMap_trace_eq_sum_algHom_of_card
    (Nat.card_eq_fintype_card.symm.trans (natCard_algHom_eq_finrank_of_etale K S L))
    Function.injective_id x
end GlobalTheory
