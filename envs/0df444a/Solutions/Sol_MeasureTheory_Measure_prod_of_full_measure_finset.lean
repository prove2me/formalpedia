-- Prove2me | solution 1 for MeasureTheory.Measure.prod_of_full_measure_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:30:15.609938+00:00
-- url     : https://prove2.me/submissions/0da1607e-2a7d-46cc-8138-29ca376b8df3

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
theorem _root_.solution {μ : Measure α} {ν : Measure β} [SigmaFinite ν]
    {A : Finset α} {B : Finset β} (hA : μ Aᶜ = 0) (hB : ν Bᶜ = 0) :
    (μ.prod ν) (A ×ˢ B : Finset (α × β))ᶜ = 0 := by
  have : (↑(A ×ˢ B) : Set (α × β))ᶜ =
    ((A : Set α)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (B : Set β)ᶜ) := by
    ext ⟨s, t⟩; simp; tauto
  simp_all
end MeasureTheory.Measure
