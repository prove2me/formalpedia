-- Prove2me | solution 1 for GlobalTheory.FourTermSumReorder.sum_four_reorder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:38.74747+00:00
-- url     : https://prove2.me/submissions/3657976e-8c8d-4d3a-9ce7-349ba49bb4fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumFourReorder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FourTermSumReorder
namespace GlobalTheory.FourTermSumReorder
theorem _root_.solution {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ b : β, ∑ a : α, ∑ c : α, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ p : β × α, ∑ q : α × β, f p.2 p.1 q.1 q.2 := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ q : α × β, ∑ p : β × α, f p.2 p.1 q.1 q.2 := Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
        simp only [Fintype.sum_prod_type]
end GlobalTheory.FourTermSumReorder
