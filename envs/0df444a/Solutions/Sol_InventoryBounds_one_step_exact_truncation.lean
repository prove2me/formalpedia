-- Prove2me | solution 1 for InventoryBounds.one_step_exact_truncation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:32:50.968125+00:00
-- url     : https://prove2.me/submissions/55e74b29-94c4-49d4-99f5-e18cc895c1a5

import Mathlib
import Definitions.Def_InventoryBounds_Primitives
set_option autoImplicit false
open InventoryBounds

theorem solution (h p y d a : ℝ) (hya : y ≤ a) :
    sales y d = sales y (min d a) ∧
    lostNext y d = lostNext y (min d a) ∧
    stageCost h p y d - stageCost h p y (min d a) = p * (d - min d a) := by
  unfold sales lostNext stageCost
  rcases le_total d a with hda | had
  · rw [min_eq_left hda]; simp
  · rw [min_eq_right had]
    have h1 : max (y - d) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (y - a) 0 = 0 := max_eq_right (by linarith)
    have h3 : max (d - y) 0 = d - y := max_eq_left (by linarith)
    have h4 : max (a - y) 0 = a - y := max_eq_left (by linarith)
    have h5 : min d y = y := min_eq_right (by linarith)
    have h6 : min a y = y := min_eq_right hya
    rw [h1, h2, h3, h4, h5, h6]
    refine ⟨rfl, rfl, ?_⟩
    ring
