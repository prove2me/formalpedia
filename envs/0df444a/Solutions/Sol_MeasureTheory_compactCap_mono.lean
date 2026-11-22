-- Prove2me | solution 1 for MeasureTheory.compactCap_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:36.552176+00:00
-- url     : https://prove2.me/submissions/84d6e1e7-a3f3-431e-b2d6-77c291b6ce2b

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set Filter Topology
namespace MeasureTheory
theorem _root_.solution
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s t : Set α} (hst : s ⊆ t) :
    MeasureTheory.compactCap μ s ≤ MeasureTheory.compactCap μ t := by
  apply sSup_le_sSup
  rintro r ⟨K, hKc, hKs, rfl⟩
  exact ⟨K, hKc, hKs.trans hst, rfl⟩
end MeasureTheory
