-- Prove2me | solution 1 for MeasureTheory.AnalyticSet.compactCap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:26.150061+00:00
-- url     : https://prove2.me/submissions/c4a467b1-1fbb-475b-bbcb-7f3ae6118e6a

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
public import Theorems.Thm_MeasureTheory_measure_isChoquetCapacity
public import Theorems.Thm_MeasureTheory_AnalyticSet_cap_eq_iSup_isCompact
section
@[expose] public section
universe u
open MeasureTheory Set Filter Topology
private lemma compactCap_eq_iSup_isCompact
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (s : Set α) :
    MeasureTheory.compactCap μ s =
      ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), μ K := by
  unfold MeasureTheory.compactCap
  apply le_antisymm
  · apply sSup_le
    rintro r ⟨K, hKc, hKs, rfl⟩
    exact le_iSup_of_le K (le_iSup_of_le hKc (le_iSup_of_le hKs le_rfl))
  · apply iSup_le; intro K
    apply iSup_le; intro hKc
    apply iSup_le; intro hKs
    apply le_csSup
    · exact ⟨μ Set.univ, fun _ ⟨_, _, _, hr⟩ => hr ▸ measure_mono (Set.subset_univ _)⟩
    · exact ⟨K, hKc, hKs, rfl⟩
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set Filter Topology
namespace MeasureTheory.AnalyticSet
theorem _root_.solution
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    MeasureTheory.compactCap μ s = μ s := by
  rw [compactCap_eq_iSup_isCompact]
  exact (hs.cap_eq_iSup_isCompact (measure_isChoquetCapacity μ)).symm
end MeasureTheory.AnalyticSet
