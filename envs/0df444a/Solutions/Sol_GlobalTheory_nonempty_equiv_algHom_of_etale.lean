-- Prove2me | solution 1 for GlobalTheory.nonempty_equiv_algHom_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:25.148606+00:00
-- url     : https://prove2.me/submissions/7ecf4d6c-2a17-4ce1-90d9-c0f6a1df4a98

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
variable (S)
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] (h : Fintype.card ι = finrank K S) :
    Nonempty (ι ≃ (S →ₐ[K] L)) := by
  have := Algebra.FormallyUnramified.finite_of_free K S
  have := Fintype.ofFinite (S →ₐ[K] L)
  rw [← Fintype.card_eq, h, ← natCard_algHom_eq_finrank_of_etale K S L, Nat.card_eq_fintype_card]
end GlobalTheory
