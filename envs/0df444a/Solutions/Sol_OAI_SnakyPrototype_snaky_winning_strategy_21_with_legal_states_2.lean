-- Prove2me | solution 2 for OAI.SnakyPrototype.snaky_winning_strategy_21_with_legal_states
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T09:02:48.279976+00:00
-- url     : https://prove2.me/submissions/5fb089ef-41bf-4a86-90c1-efafb0d05f92

import Definitions.Def_SnakyTwentyOne
import Theorems.Thm_OAI_Snaky21_empty_position_force21
import Theorems.Thm_OAI_Snaky21_force_extract
open OAI.Snaky21 OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy

theorem solution :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 21 β ∅ ∅ →
        HasSnaky (playState σ 21 β ∅ ∅ 21).1 ∧
        (playState σ 21 β ∅ ∅ 21).1.card = 21 ∧
        Disjoint (playState σ 21 β ∅ ∅ 21).1 (playState σ 21 β ∅ ∅ 20).2 ∧
        ∀ k, k < 21 →
          Disjoint (playState σ 21 β ∅ ∅ k).1 (playState σ 21 β ∅ ∅ k).2 ∧
          (playState σ 21 β ∅ ∅ k).2.card = k := by
  exact force_extract 21 (by decide) empty_position_force21
