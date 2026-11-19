-- Prove2me | solution 1 for Kyprianou.Ch01.beforeStrictUpperCrossingBoundPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:33:25.143241+00:00
-- url     : https://prove2.me/submissions/f36d5de9-03ea-44e8-ae81-ac18f337cd5b

import Mathlib.Data.NNReal.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal
set_option autoImplicit false

/-- A path cannot exceed its upper barrier strictly before first strict crossing. -/
theorem solution (f : ℝ≥0 → ℝ) (x : ℝ)
    (hstart : f 0 ≤ x) (t : ℝ≥0)
    (ht : t < sInf {u : ℝ≥0 | 0 < u ∧ x < f u}) :
    f t ≤ x := by
  classical
  let S : Set ℝ≥0 := {u | 0 < u ∧ x < f u}
  change t < sInf S at ht
  by_contra hn
  have hlt : x < f t := lt_of_not_ge hn
  have htpos : 0 < t := by
    by_contra h
    have hz : t = 0 := le_antisymm (le_of_not_gt h) (zero_le : (0 : ℝ≥0) ≤ t)
    have hf0 : x < f 0 := by simpa [hz] using hlt
    exact (not_lt_of_ge hstart) hf0
  have hmem : t ∈ S := ⟨htpos, hlt⟩
  have hle : sInf S ≤ t := csInf_le (OrderBot.bddBelow S) hmem
  exact (not_lt_of_ge hle) ht
