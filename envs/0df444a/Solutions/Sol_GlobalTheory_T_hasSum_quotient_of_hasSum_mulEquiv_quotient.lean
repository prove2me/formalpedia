-- Prove2me | solution 1 for GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:39.097877+00:00
-- url     : https://prove2.me/submissions/6d2ac3bc-4bde-45df-b260-2648fc1ebbe6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumQuotientTransport
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumQuotientTransportStatement
import Theorems.Thm_GlobalTheory_hasSum_quotient_transport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H), (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ, HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by
  first | exact @GlobalTheory.hasSum_quotient_transport | exact GlobalTheory.hasSum_quotient_transport | (intros; apply GlobalTheory.hasSum_quotient_transport <;> assumption)
end _root_.GlobalTheory.T
