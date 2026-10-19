-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.expanded_simplex_volume_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:44:47.406707+00:00
-- url     : https://prove2.me/submissions/1ff37da2-fa7f-4b6a-a1ca-c06c7e19e3ab

import Mathlib

open scoped BigOperators
theorem solution
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧
        ∑ i : Fin m, x i ≤ T + ∑ i : Fin m, w i} ≠ ⊤ := by
  apply ne_of_lt
  apply Bornology.IsBounded.measure_lt_top
  apply (Metric.isBounded_Icc (0 : Fin m → ℝ) (fun _ => T + ∑ i : Fin m, w i)).subset
  intro x hx
  obtain ⟨h0, hs⟩ := hx
  refine ⟨fun i => h0 i, fun i => ?_⟩
  calc x i ≤ ∑ j : Fin m, x j := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
    _ ≤ _ := hs
