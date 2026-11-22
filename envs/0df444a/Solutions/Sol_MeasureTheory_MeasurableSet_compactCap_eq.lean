-- Prove2me | solution 1 for MeasureTheory.MeasurableSet.compactCap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:39.863257+00:00
-- url     : https://prove2.me/submissions/70f52f05-cf85-422c-b43e-65e30b09102f

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set Filter Topology
namespace MeasureTheory.MeasurableSet
theorem _root_.solution
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) :
    MeasureTheory.compactCap μ s = μ s := by
  apply le_antisymm
  · apply sSup_le
    rintro r ⟨K, _, hKs, rfl⟩
    exact measure_mono hKs
  · change μ s ≤ MeasureTheory.compactCap μ s
    unfold MeasureTheory.compactCap
    have hbdd : BddAbove {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K} :=
      ⟨μ Set.univ, fun _ ⟨_, _, hLs, hr⟩ => hr ▸ measure_mono (hLs.trans (Set.subset_univ _))⟩
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hε_ne : (ε : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
    obtain ⟨K, hKs, hKc, hlt⟩ := hs.exists_isCompact_lt_add (measure_ne_top μ s) hε_ne
    calc μ s ≤ μ K + ε := le_of_lt hlt
      _ ≤ sSup {r | ∃ K, IsCompact K ∧ K ⊆ s ∧ r = μ K} + ε := by
        gcongr
        exact le_csSup hbdd ⟨K, hKc, hKs, rfl⟩
end MeasureTheory.MeasurableSet
