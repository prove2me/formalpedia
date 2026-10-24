-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_base
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:26:20.435042+00:00
-- url     : https://prove2.me/submissions/0772f933-306f-4dc8-8861-5af400df050b

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution (H : Real) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H}).toReal =
      H ^ 0 / ((Nat.factorial 0 : Nat) : Real) := by
  have hs : {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H} = Set.univ := by
    ext x
    simp [hH.le]
  rw [hs]
  have hvol : (MeasureTheory.volume (Set.univ : Set (Fin 0 → Real))).toReal = 1 := by
    rw [show (Set.univ : Set (Fin 0 → Real)) = Set.pi Set.univ (fun _ : Fin 0 => Set.univ) by
      ext x
      simp]
    rw [MeasureTheory.volume_pi_pi]
    simp
  rw [hvol]
  simp