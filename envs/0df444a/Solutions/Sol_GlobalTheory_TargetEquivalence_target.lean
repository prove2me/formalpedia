-- Prove2me | solution 1 for GlobalTheory.TargetEquivalence.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:35.616075+00:00
-- url     : https://prove2.me/submissions/0a290267-d57a-4648-80ba-01d84bd19a5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreFurther
import Theorems.Thm_GlobalTheory_TargetEquivalence_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetEquivalence
open Finset
namespace GlobalTheory.TargetEquivalence
theorem _root_.solution : ∀ {R α β : Type} [inst : AddCommMonoid R] [inst_1 : Fintype α] [inst_2 : Fintype β] (f : α → β → α → β → R), ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e :=
  fun f => main f
end GlobalTheory.TargetEquivalence
