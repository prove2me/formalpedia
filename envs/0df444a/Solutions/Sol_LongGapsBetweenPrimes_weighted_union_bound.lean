-- Prove2me | solution 1 for LongGapsBetweenPrimes.weighted_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:20.75916+00:00
-- url     : https://prove2.me/submissions/c042bd47-3ca7-46f3-aa21-d05f9463155a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (event : ι → Ω → Prop) [∀ i, DecidablePred (event i)]
    (hw : ∀ t, 0 ≤ w t) :
    (∑ t, w t * if ∃ i, event i t then 1 else 0) ≤
      ∑ i, ∑ t, w t * if event i t then 1 else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t _
  by_cases h : ∃ i, event i t
  · obtain ⟨i, hi⟩ := h
    simpa [show ∃ j, event j t from ⟨i, hi⟩, hi] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun j => w t * if event j t then 1 else 0)
        (fun j _ => by split_ifs <;> simp [hw]) (Finset.mem_univ i))
  · simp [not_exists.mp h]
end LongGapsBetweenPrimes
