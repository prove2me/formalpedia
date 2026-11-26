-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_infimum_decomp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:31.491308+00:00
-- url     : https://prove2.me/submissions/37694a59-a130-41f1-89cd-02ff486e92a8

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : NNReal → ℝ) (t : NNReal)
    (hbefore : ∀ s < t, 0 ≤ f s) (ht : f t ≤ 0)
    (hb : BddBelow (range f)) :
    sInf (range f) = f t +
      sInf (range fun u : NNReal => f (t + u) - f t) := by
  let g : NNReal → ℝ := fun u => f (t + u) - f t
  have hgb : BddBelow (range g) := by
    obtain ⟨a, ha⟩ := hb
    refine ⟨a - f t, ?_⟩
    rintro y ⟨u, rfl⟩
    exact sub_le_sub_right (ha ⟨t + u, rfl⟩) _
  have hg0 : sInf (range g) ≤ 0 := by
    have h := csInf_le hgb (show g 0 ∈ range g from ⟨0, rfl⟩)
    simpa [g] using h
  change sInf (range f) = f t + sInf (range g)
  apply le_antisymm
  · have hlow : sInf (range f) - f t ≤ sInf (range g) := by
      apply le_csInf (range_nonempty g)
      rintro y ⟨u, rfl⟩
      exact sub_le_sub_right (csInf_le hb ⟨t + u, rfl⟩) _
    linarith
  · apply le_csInf (range_nonempty f)
    rintro y ⟨s, rfl⟩
    by_cases hs : s < t
    · linarith [hbefore s hs]
    · have hts : t ≤ s := le_of_not_gt hs
      have h := csInf_le hgb (show g (s - t) ∈ range g from ⟨s - t, rfl⟩)
      change sInf (range g) ≤ f (t + (s - t)) - f t at h
      rw [add_comm t, tsub_add_cancel_of_le hts] at h
      linarith
