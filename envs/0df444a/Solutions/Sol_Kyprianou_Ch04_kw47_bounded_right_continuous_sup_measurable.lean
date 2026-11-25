-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_bounded_right_continuous_sup_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T14:25:11.747111+00:00
-- url     : https://prove2.me/submissions/4b294e58-1c33-4c7c-bf50-a6ae7e47f220

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega] (f : NNReal → Omega → Real)
    (hm : ∀ t, Measurable (f t))
    (hr : ∀ w t, ContinuousWithinAt (fun s => f s w) (Ici t) t)
    (t : NNReal)
    (hb : ∀ w, BddAbove ((fun s => f s w) '' Iic t)) :
    Measurable (fun w => sSup ((fun s => f s w) '' Iic t)) := by 
  classical
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (α := NNReal)
  let S := insert (0 : NNReal) (range u)
  have hS : Dense S := hu.mono (subset_insert _ _)
  have hc : S.Countable := (countable_range u).insert _
  haveI : Countable {s : NNReal // s ∈ S ∧ s ≤ t} :=
    (hc.mono (fun _ h => h.1)).to_subtype
  have heq (w : Omega) :
      sSup ((fun s => f s w) '' Iic t) =
        ⨆ s : Icc (0 : NNReal) t, f s.1 w := by
    change sSup _ = sSup _
    congr 1
    ext z
    simp only [mem_image, mem_range, Subtype.exists, mem_Icc,
      mem_Iic, zero_le, true_and, exists_prop]
  have hrep (w : Omega) := AvramDividend.Classical.dense_timeSup_with_endpoint
    (fun s => f s w) (hr w) S hS (mem_insert _ _) t
    (show BddAbove (range (fun s : Icc (0 : NNReal) t => f s.1 w)) from
      (hb w).mono (by rintro _ ⟨s, rfl⟩; exact ⟨s.1, s.2.2, rfl⟩))
  simp_rw [heq, hrep]
  exact (Measurable.iSup (fun s : {s : NNReal // s ∈ S ∧ s ≤ t} => hm s.1)).max (hm t)
