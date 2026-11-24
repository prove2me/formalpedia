-- Prove2me | solution 1 for Kyprianou.Ch03.prod_countable_measurable_left_rectanglesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T10:49:22.449948+00:00
-- url     : https://prove2.me/submissions/a8d2096f-d3d1-4fba-85ef-72b047a9c125

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Omega OmegaE I : Type} [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    [Countable I] (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : I → Set Omega) (B : I → Set OmegaE)
    (hA : ∀ i, MeasurableSet (A i)) :
    (P.prod Q) (⋃ i, A i ×ˢ B i) =
      ∫⁻ omega, Q (⋃ i : {i // omega ∈ A i}, B i.1) ∂P := by
  classical
  let S : Set (Omega × OmegaE) := ⋃ i, A i ×ˢ B i
  let R : Set (Omega × OmegaE) := ⋃ i, A i ×ˢ toMeasurable Q (B i)
  have hSR : S ⊆ R := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨i, hi.1, subset_toMeasurable Q (B i) hi.2⟩
  have hR : MeasurableSet R :=
    MeasurableSet.iUnion (fun i => (hA i).prod (measurableSet_toMeasurable Q (B i)))
  have hsec (omega : Omega) :
      Prod.mk omega ⁻¹' R =
        ⋃ i : {i // omega ∈ A i}, toMeasurable Q (B i.1) := by
    ext eta
    simp only [R, Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Subtype.exists]
    exact ⟨fun ⟨i, hi, hj⟩ => ⟨i, hi, hj⟩, fun ⟨i, hi, hj⟩ => ⟨i, hi, hj⟩⟩
  have hsecS (omega : Omega) :
      Prod.mk omega ⁻¹' S = ⋃ i : {i // omega ∈ A i}, B i.1 := by
    ext eta
    simp only [S, Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Subtype.exists]
    exact ⟨fun ⟨i, hi, hj⟩ => ⟨i, hi, hj⟩, fun ⟨i, hi, hj⟩ => ⟨i, hi, hj⟩⟩
  change (P.prod Q) S = _
  apply le_antisymm
  · calc
      (P.prod Q) S ≤ (P.prod Q) R := measure_mono hSR
      _ = ∫⁻ omega, Q (Prod.mk omega ⁻¹' R) ∂P := Measure.prod_apply hR
      _ = _ := by
        apply lintegral_congr
        intro omega
        rw [hsec]
        exact measure_iUnion_toMeasurable (μ := Q) (fun i : {i // omega ∈ A i} => B i.1)
  · calc
      (∫⁻ omega, Q (⋃ i : {i // omega ∈ A i}, B i.1) ∂P)
          ≤ ∫⁻ omega, Q (Prod.mk omega ⁻¹' toMeasurable (P.prod Q) S) ∂P := by
              apply lintegral_mono
              intro omega
              change Q (⋃ i : {i // omega ∈ A i}, B i.1) ≤
                Q (Prod.mk omega ⁻¹' toMeasurable (P.prod Q) S)
              rw [← hsecS omega]
              exact measure_mono (fun eta h => subset_toMeasurable (P.prod Q) S h)
      _ = (P.prod Q) (toMeasurable (P.prod Q) S) :=
        (Measure.prod_apply (measurableSet_toMeasurable (P.prod Q) S)).symm
      _ = (P.prod Q) S := measure_toMeasurable _
