-- Prove2me | solution 1 for Kyprianou.Ch04.rangeSupSuccRealV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:39:49.803814+00:00
-- url     : https://prove2.me/submissions/a452b14c-ae6b-4564-b79b-6a4fc9d50d83

import Mathlib
set_option autoImplicit false
/-- Split a nonempty finite prefix supremum into its final term and earlier prefix. -/
theorem solution (a : ℕ → ℝ) (n : ℕ) :
    (Finset.range (n+1+1)).sup' Finset.nonempty_range_add_one a =
      a (n+1) ⊔ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one a := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    by_cases h : j = n+1
    · subst j
      exact le_sup_left
    · have hj' : j < n+1 := by
        have := Finset.mem_range.mp hj
        omega
      exact (Finset.le_sup' a (Finset.mem_range.mpr hj')).trans le_sup_right
  · apply sup_le
    · exact Finset.le_sup' a (show n+1 ∈ Finset.range (n+1+1) from
        Finset.mem_range.mpr (Nat.lt_succ_self _))
    · apply Finset.sup'_le
      intro j hj
      exact Finset.le_sup' a (show j ∈ Finset.range (n+1+1) from
        Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans (Nat.lt_succ_self _)))
