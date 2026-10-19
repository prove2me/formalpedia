-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_lattice_box_measure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:44:40.54554+00:00
-- url     : https://prove2.me/submissions/f2982212-97ef-42e7-bd18-87b19cd1a820

import Mathlib

open scoped BigOperators
theorem solution
    (m : ℕ) (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (a : Fin m → ℕ) :
    MeasurableSet
        {x : Fin m → ℝ | ∀ i,
          w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)} ∧
      MeasureTheory.volume
          {x : Fin m → ℝ | ∀ i,
            w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)} =
        ∏ i : Fin m, ENNReal.ofReal (w i) := by
  have hset : {x : Fin m → ℝ | ∀ i, w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)} =
      Set.pi Set.univ (fun i => Set.Ico (w i * (a i : ℝ)) (w i * ((a i : ℝ) + 1))) := by
    ext x; simp [Set.mem_pi]
  rw [hset]
  refine ⟨MeasurableSet.univ_pi (fun i => measurableSet_Ico), ?_⟩
  rw [Real.volume_pi_Ico]
  apply Finset.prod_congr rfl; intro i _
  congr 1; ring
