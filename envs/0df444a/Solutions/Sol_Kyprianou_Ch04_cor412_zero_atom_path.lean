-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_zero_atom_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:31.665724+00:00
-- url     : https://prove2.me/submissions/3846c82a-175f-4730-8b3d-8a6b6baa5d60

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : NNReal → ℝ) (h0 : f 0 = 0) (hb : BddBelow (range f)) :
    -sInf (range f) = 0 ↔ ∀ t : NNReal, 0 ≤ f t := by
  have hi : sInf (range f) ≤ 0 := by
    rw [← h0]
    exact csInf_le hb ⟨0, rfl⟩
  constructor
  · intro hz t
    have ht := csInf_le hb (show f t ∈ range f from ⟨t, rfl⟩)
    linarith
  · intro h
    have hlo : 0 ≤ sInf (range f) := by
      apply le_csInf (range_nonempty f)
      rintro y ⟨t, rfl⟩
      exact h t
    linarith
