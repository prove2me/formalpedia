-- Prove2me | solution 1 for N4Code.count_pos_of_colVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:55.842997+00:00
-- url     : https://prove2.me/submissions/03ba2b44-473a-4323-8827-53bb16c0d8b2

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_fiber_card_eq_count


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) {i : ℕ} (t : Fin n) (h : colVal (C t) = i) :
    1 ≤ count C i := by
  have ht : t ∈ fiber C i := by simp [fiber, h]
  rw [← fiber_card_eq_count]
  exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨t, ht⟩)
end N4Code
