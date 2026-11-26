-- Prove2me | solution 1 for Kyprianou.Ch04.finiteWindowRandomMeasureVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:23:35.774868+00:00
-- url     : https://prove2.me/submissions/f9b872a2-e993-4de8-892d-7fb28285af99

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

/-- A random measure on a finite window admits a pointwise finite measurable version. -/
theorem solution {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (N : Ω → Measure E) (D : Set E) (hD : MeasurableSet D)
    (hPast : ∀ S : Set E, MeasurableSet S → S ⊆ D → Measurable (fun w => N w S))
    (hFin : ∀ᵐ w ∂P, N w D < ⊤) :
    ∃ R : Ω → Measure E, (∀ w, IsFiniteMeasure (R w)) ∧
      (∀ S : Set E, MeasurableSet S → Measurable (fun w => R w S)) ∧
      ∀ᵐ w ∂P, R w = (N w).restrict D := by
  classical
  let A := {w | N w D < ⊤}
  have hA : MeasurableSet A := measurableSet_lt (hPast D hD subset_rfl) measurable_const
  let R : Ω → Measure E := fun w => if w ∈ A then (N w).restrict D else 0
  refine ⟨R,?_,?_,?_⟩
  · intro w
    by_cases hw : w ∈ A
    · rw [show R w = (N w).restrict D from if_pos hw]
      exact ⟨by simpa only [Measure.restrict_apply_univ] using (show N w D < ⊤ from hw)⟩
    · rw [show R w = 0 from if_neg hw]
      infer_instance
  · intro S hS
    have hm := hPast (S ∩ D) (hS.inter hD) inter_subset_right
    have he : (fun w => R w S) = A.indicator (fun w => N w (S ∩ D)) := by
      funext w
      by_cases hw : w ∈ A <;> simp [R,hw,Measure.restrict_apply hS]
    rw [he]
    exact hm.indicator hA
  · filter_upwards [hFin] with w hw
    exact if_pos hw
