-- Prove2me | solution 1 for GlobalTheory.IsOrderingRule.length_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:56:02.98906+00:00
-- url     : https://prove2.me/submissions/875cf5d2-2619-44c9-9a29-4cc775b3233f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finsupp
variable {R : Type*} [CommRing R] {Λ : Type*} {B : Type*} [Ring B] [Algebra R B]
namespace GlobalTheory
namespace IsOrderingRule
theorem _root_.solution {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord)
    (α : Λ →₀ ℕ) : (ord α).length = degree α := by
  rw [← Multiset.coe_card, h α, Finsupp.card_toMultiset]
  rfl
end IsOrderingRule
end GlobalTheory
