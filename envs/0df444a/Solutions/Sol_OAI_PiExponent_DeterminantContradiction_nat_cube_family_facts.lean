-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.nat_cube_family_facts
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:43:17.079757+00:00
-- url     : https://prove2.me/submissions/1fb1584e-1bce-4a64-bf8e-713ec93c4e99

import Mathlib

open scoped BigOperators

theorem solution {m : ℕ} (S : Finset (Fin m → ℕ)) :
    (∀ a ∈ S, MeasurableSet
      {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1}) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      Disjoint
        {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1}
        {x : Fin m → ℝ | ∀ i, (b i : ℝ) ≤ x i ∧ x i < (b i : ℝ) + 1}) ∧
    (∀ a ∈ S, MeasureTheory.volume
      {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    have hset :
        {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} =
          Set.pi Set.univ (fun i => Set.Ico (a i : ℝ) ((a i : ℝ) + 1)) := by
      ext x
      simp [Set.mem_Ico]
    rw [hset]
    exact MeasurableSet.univ_pi (fun i => measurableSet_Ico)
  · intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    have hdiff : ∃ i, a i ≠ b i := by
      by_contra h
      push_neg at h
      exact hab (funext h)
    obtain ⟨i, hne⟩ := hdiff
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgap : (a i : ℝ) + 1 ≤ (b i : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      exact (not_lt_of_ge (hxb i).1) ((hxa i).2.trans_le hgap)
    · have hgap : (b i : ℝ) + 1 ≤ (a i : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hgt)
      exact (not_lt_of_ge (hxa i).1) ((hxb i).2.trans_le hgap)
  · intro a ha
    have hset :
        {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} =
          Set.pi Set.univ (fun i => Set.Ico (a i : ℝ) ((a i : ℝ) + 1)) := by
      ext x
      simp [Set.mem_Ico]
    rw [hset, Real.volume_pi_Ico]
    apply Finset.prod_eq_one
    intro i hi
    norm_num