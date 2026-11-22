-- Prove2me | solution 1 for MeasureTheory.Measure.prod_apply_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:23.940203+00:00
-- url     : https://prove2.me/submissions/fe033fcb-6c32-4f16-885d-5cd8cec4b267

module
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod

set_option autoImplicit true
@[expose] public section
public section
open Function
open scoped ENNReal NNReal
open MeasureTheory MeasureTheory.Measure
variable {Ω α β γ : Type*} [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {X : Ω → α} {Y : Ω
    → β} {Z : Ω → γ}
namespace MeasureTheory.Measure
theorem _root_.solution {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν) {x} = μ {x.1} * ν {x.2} := by
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Measure.prod_prod]
end MeasureTheory.Measure
