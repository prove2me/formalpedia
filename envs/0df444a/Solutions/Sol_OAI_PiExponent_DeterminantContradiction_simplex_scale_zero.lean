-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_scale_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:38:41.501432+00:00
-- url     : https://prove2.me/submissions/7d251342-3bdb-41b8-9704-90084df8b32a

import Mathlib

open scoped BigOperators

theorem solution (k : ℕ) :
    (MeasureTheory.volume
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 0}).toReal =
      (0 ^ k) * (MeasureTheory.volume
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}).toReal := by
  cases k with
  | zero =>
      have h₀ :
          {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ 0} = Set.univ := by
        ext x
        simp
      have h₁ :
          {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ 1} = Set.univ := by
        ext x
        simp
      have hv : (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [MeasureTheory.Measure.volume_pi_eq_dirac]
        simp
      rw [h₀, h₁, hv]
      norm_num
  | succ n =>
      have hset :
          {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ 0} =
            ({0} : Set (Fin (n + 1) → ℝ)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hx
          have hsum : (∑ i : Fin (n + 1), x i) = 0 :=
            le_antisymm hx.2 (Finset.sum_nonneg fun i hi => hx.1 i)
          funext i
          apply le_antisymm
          · have hle : x i ≤ ∑ j : Fin (n + 1), x j :=
              Finset.single_le_sum (fun j hj => hx.1 j) (Finset.mem_univ i)
            simpa [hsum] using hle
          · exact hx.1 i
        · intro hx
          subst x
          simp
      have hv :
          MeasureTheory.volume ({0} : Set (Fin (n + 1) → ℝ)) = 0 := by
        simp
      rw [hset, hv]
      simp