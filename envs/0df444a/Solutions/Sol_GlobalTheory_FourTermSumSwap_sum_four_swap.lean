-- Prove2me | solution 1 for GlobalTheory.FourTermSumSwap.sum_four_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:43.512608+00:00
-- url     : https://prove2.me/submissions/48ad3734-4f81-49a8-934e-4f0ece3d63a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumFourSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FourTermSumSwap
namespace GlobalTheory.FourTermSumSwap
theorem _root_.solution : ∀ {R α β : Type} [inst : AddCommMonoid R] [inst_1 : Fintype α] [inst_2 : Fintype β]
    (f : α → β → α → β → R),
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
  intro R α β _ _ _ f
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ b : β, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
end GlobalTheory.FourTermSumSwap
