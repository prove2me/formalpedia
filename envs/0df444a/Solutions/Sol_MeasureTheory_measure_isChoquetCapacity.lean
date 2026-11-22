-- Prove2me | solution 1 for MeasureTheory.measure_isChoquetCapacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:37.338521+00:00
-- url     : https://prove2.me/submissions/66093a5a-0eac-4101-bca6-2ad3e4ce0c0c

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
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ] :
    MeasureTheory.IsChoquetCapacity (fun s : Set α => μ s) := by
  constructor
  · intro s t hst; exact measure_mono hst
  · intro f hf; exact hf.measure_iUnion
  · intro f hf hclosed
    exact hf.measure_iInter
      (fun n => (hclosed n).measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top μ (f 0)⟩
end MeasureTheory
