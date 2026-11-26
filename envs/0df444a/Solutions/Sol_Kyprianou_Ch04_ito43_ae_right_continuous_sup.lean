-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ae_right_continuous_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:22:07.270938+00:00
-- url     : https://prove2.me/submissions/f738e1af-c7e4-462e-896b-85ef8a895daa

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (E : NNReal → Ω → ℝ) (T : NNReal)
    (hm : ∀ t, AEMeasurable (E t) P)
    (hr : ∀ᵐ w ∂P, (∀ t, ContinuousWithinAt (fun s => |E s w|) (Ici t) t) ∧
      BddAbove (range (fun t : Iic T => |E t w|))) :
    AEStronglyMeasurable (fun w => sSup (range (fun t : Iic T => |E t w|))) P := by
  classical
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (α := NNReal)
  let S := insert (0 : NNReal) (range u)
  have hS : Dense S := hu.mono (subset_insert _ _)
  have hc : S.Countable := (countable_range u).insert _
  haveI : Countable {s : NNReal // s ∈ S ∧ s ≤ T} :=
    (hc.mono (fun _ h => h.1)).to_subtype
  let D : Ω → ℝ := fun w =>
    max (⨆ s : {s : NNReal // s ∈ S ∧ s ≤ T}, |E s.1 w|) (|E T w|)
  have hD : AEMeasurable D P :=
    (AEMeasurable.iSup (fun s : {s : NNReal // s ∈ S ∧ s ≤ T} =>
      (hm s.1).abs)).max (hm T).abs
  apply hD.aestronglyMeasurable.congr
  filter_upwards [hr] with w hw
  have heq : sSup (range (fun t : Iic T => |E t w|)) =
      (⨆ s : Icc (0 : NNReal) T, |E s.1 w|) := by
    change sSup _ = sSup _
    congr 1
    ext z
    simp only [mem_range, Subtype.exists, mem_Icc, mem_Iic, zero_le, true_and]
  have hb : BddAbove (range (fun s : Icc (0 : NNReal) T => |E s.1 w|)) :=
    hw.2.mono (by rintro _ ⟨s,rfl⟩; exact ⟨⟨s.1,s.2.2⟩,rfl⟩)
  symm
  rw [heq, AvramDividend.Classical.dense_timeSup_with_endpoint
    (fun t => |E t w|) hw.1 S hS (mem_insert _ _) T hb]
