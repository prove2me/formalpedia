-- Prove2me | solution 1 for N4Code.exists_subset_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:42.070998+00:00
-- url     : https://prove2.me/submissions/8a11d974-3265-4939-af94-453258fe90a0

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {α : Type*} [DecidableEq α] {s : Finset α} {k : ℕ}
    (hk : k ≤ s.card) : ∃ t : Finset α, t ⊆ s ∧ t.card = k := by
  rcases Finset.powersetCard_nonempty_of_le hk with ⟨t, ht⟩
  exact ⟨t, Finset.mem_powersetCard.mp ht⟩
end N4Code
