-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_unit
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:43:42.546634+00:00
-- url     : https://prove2.me/submissions/e523b34b-7c1c-40eb-8fb9-61755e18f11c

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_volume_succ

open scoped BigOperators

theorem solution (m : ℕ) :
    (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ 1}).toReal =
      (1 : ℝ) / (Nat.factorial m : ℝ) := by
  have hzero :
      (MeasureTheory.volume (Set.univ : Set (Fin 0 → ℝ))).toReal = 1 := by
    have hset : (Set.univ : Set (Fin 0 → ℝ)) =
        Set.pi Set.univ (fun _ : Fin 0 => (Set.univ : Set ℝ)) := by
      ext x
      simp
    rw [hset, MeasureTheory.volume_pi_pi]
    simp
  induction m with
  | zero =>
      simpa using hzero
  | succ m ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_succ, ih,
        Nat.factorial_succ]
      push_cast
      field_simp