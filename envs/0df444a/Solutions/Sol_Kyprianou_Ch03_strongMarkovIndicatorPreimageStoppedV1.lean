-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovIndicatorPreimageStoppedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:21:37.839136+00:00
-- url     : https://prove2.me/submissions/efa0b978-b8b0-41c2-adc5-9627f2142d34

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (A : Set Omega) (hA : (∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w : Omega | tau w ≤ (s : WithTop NNReal)})))
    (S : Set Real) (hS : MeasurableSet S) :
    ∀ s : NNReal, MeasurableSet[F s]
      ((Set.indicator A (fun _ : Omega => (1 : Real)) ⁻¹' S) ∩
        {w : Omega | tau w ≤ (s : WithTop NNReal)}) := by
  classical
  intro s
  let C := {w : Omega | tau w ≤ (s : WithTop NNReal)}
  have hm : Measurable[F s] (Set.indicator (A ∩ C) (fun _ : Omega => (1 : ℝ))) :=
    measurable_const.indicator (hA s)
  have he : (Set.indicator A (fun _ : Omega => (1 : ℝ)) ⁻¹' S) ∩ C =
      (Set.indicator (A ∩ C) (fun _ : Omega => (1 : ℝ))) ⁻¹' S ∩ C := by
    ext w
    by_cases hc : w ∈ C <;> simp [Set.indicator, hc]
  rw [he]
  exact (hm hS).inter (hTau s)
