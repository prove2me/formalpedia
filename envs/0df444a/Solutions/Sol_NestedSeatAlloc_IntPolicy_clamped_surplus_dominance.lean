-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.clamped_surplus_dominance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:45:38.31548+00:00
-- url     : https://prove2.me/submissions/b0c44b1c-266e-44d8-b2fe-824bd99b5fa9

import Mathlib
import Theorems.Thm_NestedSeatAlloc_IntPolicy_clamped_surplus_optimal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy

theorem solution
    (gq gp : ℝ → ℝ) (c a s y b : ℝ)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hy : 0 ≤ y) (hb : 0 ≤ b)
    (hdom : ∀ t, 0 ≤ t → gq t ≤ gp t)
    (hleft : ∀ u v, 0 ≤ u → u ≤ v → v ≤ a →
      gp u - c * u ≤ gp v - c * v)
    (hright : ∀ u v, a ≤ u → u ≤ v →
      gp v - c * v ≤ gp u - c * u) :
    c * min (max (s - b) 0) y + gq (s - min (max (s - b) 0) y) ≤
    c * min (max (s - a) 0) y + gp (s - min (max (s - a) 0) y) := by
  have hub : min (max (s - b) 0) y ≤ s := by
    calc
      min (max (s - b) 0) y ≤ max (s - b) 0 := min_le_left _ _
      _ ≤ s := max_le (by linarith) hs
  have hres : 0 ≤ s - min (max (s - b) 0) y := by
    linarith
  have hvalue := hdom (s - min (max (s - b) 0) y) hres
  calc
    c * min (max (s - b) 0) y +
      gq (s - min (max (s - b) 0) y) ≤
        c * min (max (s - b) 0) y +
          gp (s - min (max (s - b) 0) y) := by
      linarith only [hvalue]
    _ ≤ c * min (max (s - a) 0) y +
      gp (s - min (max (s - a) 0) y) :=
      clamped_surplus_optimal gp c a s y b ha hs hy hb hleft hright
