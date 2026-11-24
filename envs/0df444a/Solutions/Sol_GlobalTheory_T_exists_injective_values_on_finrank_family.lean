-- Prove2me | solution 1 for GlobalTheory.T.exists_injective_values_on_finrank_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:06:07.581878+00:00
-- url     : https://prove2.me/submissions/f8cac0b9-bb16-47fb-8472-94540eecfbce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Theorems.Thm_GlobalTheory_finrank_le_card_values


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C V Γ : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u = ν v → ∃ c : C, u - c • v = 0 ∨ ν u < ν (u - c • v)) → ∀ (F : Submodule C V) [Module.Finite C F], ∃ f : Fin (Module.finrank C F) → V, (∀ i, f i ∈ F ∧ f i ≠ 0) ∧ Function.Injective (fun i => ν (f i)) := by
  first | exact @GlobalTheory.finrank_le_card_values | exact GlobalTheory.finrank_le_card_values | (intros; apply GlobalTheory.finrank_le_card_values <;> assumption)
end _root_.GlobalTheory.T
