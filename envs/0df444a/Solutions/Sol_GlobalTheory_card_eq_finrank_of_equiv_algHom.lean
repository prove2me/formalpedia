-- Prove2me | solution 1 for GlobalTheory.card_eq_finrank_of_equiv_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:49.788229+00:00
-- url     : https://prove2.me/submissions/66658251-0ef8-4395-8b24-a01fc40a4772

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin

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
theorem _root_.solution (P : ι ≃ (S →ₐ[K] L)) : Fintype.card ι = finrank K S := by
  rw [← natCard_algHom_eq_finrank_of_etale K S L, ← Nat.card_congr P, Nat.card_eq_fintype_card]
end GlobalTheory
