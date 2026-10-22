-- Prove2me | solution 1 for InventoryBounds.carry_cap_closure
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:28:47.162145+00:00
-- url     : https://prove2.me/submissions/6f71ae83-d99f-4069-8f8e-1ba9495c3c66

import Mathlib
import Definitions.Def_InventoryBounds_Primitives
set_option autoImplicit false
open InventoryBounds

theorem solution (x s d a b : ℝ)
    (hx : x ≤ a) (hs : s ≤ a) (hd : 0 ≤ d)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    max x s ≤ a ∧ lostNext (max x s) d ≤ b := by
  have hm : max x s ≤ a := max_le hx hs
  refine ⟨hm, ?_⟩
  unfold lostNext
  exact max_le (by linarith) (by linarith)
