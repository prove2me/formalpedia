-- Prove2me | solution 1 for Kyprianou.Ch04.predictableGridCellV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:56:06.714721+00:00
-- url     : https://prove2.me/submissions/17018288-5588-40df-b10d-200f788a5f89

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance) (a b : NNReal) (H : Ω → ℝ)
    (hH : Measurable[F a] H) :
    Measurable[F.predictable] ((Ioc a b ×ˢ (univ : Set Ω)).indicator
      (fun p : NNReal × Ω => H p.2)) := by
  letI : MeasurableSpace (NNReal × Ω) := F.predictable
  intro S hS
  let A := Ioc a b ×ˢ (univ : Set Ω)
  have hA : MeasurableSet A :=
    measurableSet_predictable_Ioc_prod (𝓕 := F) a b MeasurableSet.univ
  have hB : MeasurableSet (Ioc a b ×ˢ (H ⁻¹' S)) :=
    measurableSet_predictable_Ioc_prod (𝓕 := F) a b (hH hS)
  by_cases h0 : (0 : ℝ) ∈ S
  · have he : (A.indicator (fun p : NNReal × Ω => H p.2)) ⁻¹' S =
        (Ioc a b ×ˢ (H ⁻¹' S)) ∪ Aᶜ := by
      ext p
      by_cases hp : p ∈ A
      · have ht : p.1 ∈ Ioc a b := hp.1
        simp [Set.indicator_of_mem hp, hp, ht]
      · have ht : p.1 ∉ Ioc a b := fun h => hp ⟨h, mem_univ _⟩
        simp [Set.indicator_of_notMem hp, hp, ht, h0]
    change MeasurableSet ((A.indicator _) ⁻¹' S)
    rw [he]
    exact hB.union hA.compl
  · have he : (A.indicator (fun p : NNReal × Ω => H p.2)) ⁻¹' S =
        Ioc a b ×ˢ (H ⁻¹' S) := by
      ext p
      by_cases hp : p ∈ A
      · have ht : p.1 ∈ Ioc a b := hp.1
        simp [Set.indicator_of_mem hp, ht]
      · have ht : p.1 ∉ Ioc a b := fun h => hp ⟨h, mem_univ _⟩
        simp [Set.indicator_of_notMem hp, ht, h0]
    change MeasurableSet ((A.indicator _) ⁻¹' S)
    rw [he]
    exact hB
