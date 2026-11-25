-- Prove2me | solution 1 for Kyprianou.Ch04.bvRestrictedDiracIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:59:36.535435+00:00
-- url     : https://prove2.me/submissions/df4c83ee-078f-466e-8a40-727a3ceceec3

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {I : Type} [Countable I] (φ : I → ℝ × ℝ)
    (B : Set (ℝ × ℝ)) (hB : MeasurableSet B) (g : ℝ × ℝ → ℝ) :
    (∫ z in B, g z ∂(Measure.sum (fun s : I => Measure.dirac (φ s)))) =
      ∑' s : I, B.indicator g (φ s) := by
  classical
  let w : I → ENNReal := fun s => if φ s ∈ B then 1 else 0
  rw [Measure.restrict_sum _ hB]
  have hw : (Measure.sum fun s : I => (Measure.dirac (φ s)).restrict B) =
      Measure.sum (fun s : I => w s • Measure.dirac (φ s)) := by
    congr 1
    funext s
    rw [restrict_dirac]
    by_cases hs : φ s ∈ B <;> simp [w, hs]
  rw [hw, integral_sum_dirac (c := w) (x := φ) (f := g)
    (fun s => by by_cases hs : φ s ∈ B <;> simp [w, hs])]
  apply tsum_congr
  intro s
  by_cases hs : φ s ∈ B <;> simp [w, Set.indicator_apply, hs]
