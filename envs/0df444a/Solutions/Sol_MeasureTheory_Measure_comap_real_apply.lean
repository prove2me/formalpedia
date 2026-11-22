-- Prove2me | solution 1 for MeasureTheory.Measure.comap_real_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:34.557138+00:00
-- url     : https://prove2.me/submissions/65294be0-1e45-4fff-b2e9-3514a4d8b88a

module
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real

set_option autoImplicit true
@[expose] public section
public section
open Function Set
open scoped ENNReal NNReal
open MeasureTheory
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}
namespace MeasureTheory
namespace _root_.MeasureTheory.Measure
theorem _root_.solution {s : Set α} {f : α → β} (hfi : Injective f)
    (hf : ∀ s,
      MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    (Measure.comap f μ).real s = μ.real (f '' s) := by
  simp [Measure.real, Measure.comap_apply _ hfi hf μ hs]
end _root_.MeasureTheory.Measure
end MeasureTheory
