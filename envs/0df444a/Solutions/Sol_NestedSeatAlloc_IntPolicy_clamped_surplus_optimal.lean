-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.clamped_surplus_optimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:37:25.519343+00:00
-- url     : https://prove2.me/submissions/5b803ec4-45b5-44b2-a328-91177366eb6a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy

theorem solution (g : ℝ → ℝ) (c a s y b : ℝ)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hy : 0 ≤ y) (hb : 0 ≤ b)
    (hleft : ∀ u v, 0 ≤ u → u ≤ v → v ≤ a →
      g u - c * u ≤ g v - c * v)
    (hright : ∀ u v, a ≤ u → u ≤ v →
      g v - c * v ≤ g u - c * u) :
    c * min (max (s - b) 0) y + g (s - min (max (s - b) 0) y) ≤
    c * min (max (s - a) 0) y + g (s - min (max (s - a) 0) y) := by
  let ua : ℝ := min (max (s - a) 0) y
  let ub : ℝ := min (max (s - b) 0) y
  let ta : ℝ := s - ua
  let tb : ℝ := s - ub
  change c * ub + g (s - ub) ≤ c * ua + g (s - ua)
  have hub_nonneg : 0 ≤ ub := by
    dsimp [ub]
    exact le_min (le_max_right _ _) hy
  have hub_le_s : ub ≤ s := by
    calc
      ub ≤ max (s - b) 0 := min_le_left _ _
      _ ≤ s := max_le (by linarith) hs
  have hub_le_y : ub ≤ y := min_le_right _ _
  have htb_nonneg : 0 ≤ tb := by
    change 0 ≤ s - ub
    linarith
  have htb_low : s - y ≤ tb := by
    change s - y ≤ s - ub
    linarith
  have hcomp : g tb - c * tb ≤ g ta - c * ta := by
    by_cases hsa : s ≤ a
    · have hua : ua = 0 := by
        dsimp [ua]
        rw [max_eq_right (by linarith : s - a ≤ (0 : ℝ)), min_eq_left hy]
      have hta : ta = s := by
        change s - ua = s
        rw [hua]
        ring
      apply hleft tb ta htb_nonneg
      · rw [hta]
        change s - ub ≤ s
        linarith
      · rw [hta]
        exact hsa
    · by_cases halow : a ≤ s - y
      · have hua : ua = y := by
          dsimp [ua]
          rw [max_eq_left (by linarith : (0 : ℝ) ≤ s - a),
            min_eq_right (by linarith : y ≤ s - a)]
        have hta : ta = s - y := by
          change s - ua = s - y
          rw [hua]
        apply hright ta tb
        · rw [hta]
          exact halow
        · rw [hta]
          exact htb_low
      · have hua : ua = s - a := by
          dsimp [ua]
          rw [max_eq_left (by linarith : (0 : ℝ) ≤ s - a),
            min_eq_left (by linarith : s - a ≤ y)]
        have hta : ta = a := by
          change s - ua = a
          rw [hua]
          ring
        by_cases hba : tb ≤ a
        · apply hleft tb ta htb_nonneg
          · rw [hta]
            exact hba
          · rw [hta]
        · apply hright ta tb
          · rw [hta]
          · rw [hta]
            exact le_of_lt (lt_of_not_ge hba)
  calc
    c * ub + g (s - ub) = c * s + (g tb - c * tb) := by
      change c * ub + g (s - ub) = c * s + (g (s - ub) - c * (s - ub))
      ring
    _ ≤ c * s + (g ta - c * ta) := by
      linarith only [hcomp]
    _ = c * ua + g (s - ua) := by
      change c * s + (g (s - ua) - c * (s - ua)) = c * ua + g (s - ua)
      ring
