-- Prove2me | solution 1 for GlobalTheory.card_record_indices_le_of_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:58.04674+00:00
-- url     : https://prove2.me/submissions/6ad432f0-cca0-4bd5-a7f7-ae3cc1f45908

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ChainLengthBoundOfSupInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {α : Type} [Preorder α] (Q : α → Prop) (L : ℕ)
    (h : ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q (N i)) → r ≤ L)
    {r : ℕ} (a : Fin r → α) (ha : ∀ i, Q (a i)) (T : Finset (Fin r))
    (hT : ∀ j ∈ T, ∀ i < j, a i < a j) : T.card ≤ L := by
  refine h T.card (fun k => a (T.orderEmbOfFin rfl k)) ?_ (fun k => ha _)
  intro k k' hk
  exact hT _ (T.orderEmbOfFin_mem rfl k') _ ((T.orderEmbOfFin rfl).strictMono hk)
end GlobalTheory
