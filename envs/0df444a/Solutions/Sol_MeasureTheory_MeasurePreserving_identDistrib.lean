-- Prove2me | solution 1 for MeasureTheory.MeasurePreserving.identDistrib
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:44:00.5578+00:00
-- url     : https://prove2.me/submissions/d8d2c65a-b571-47d9-915d-f911ee386b47

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Measure Filter Set
open scoped Topology MeasureTheory ENNReal NNReal
attribute [symm] ProbabilityTheory.IdentDistrib.symm
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]
open ProbabilityTheory
variable {μ : Measure α} {ν : Measure β} {f f' : α → γ} {g g' : β → γ} {s : Set γ}
namespace ProbabilityTheory
namespace _root_.MeasureTheory.MeasurePreserving
theorem _root_.solution {α β γ : Type*} {X : β
  → γ} {f : α → β}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure α}
    {ν : Measure β} (hf : MeasurePreserving f μ ν) (hX : AEMeasurable X ν) :
    IdentDistrib X (X ∘ f) ν μ := by
  have A : AEMeasurable X (Measure.map f μ) := by rwa [hf.map_eq]
  constructor
  · exact hX
  · exact AEMeasurable.comp_aemeasurable A hf.aemeasurable
  · rw [← AEMeasurable.map_map_of_aemeasurable A hf.aemeasurable, hf.map_eq]
end _root_.MeasureTheory.MeasurePreserving
end ProbabilityTheory
