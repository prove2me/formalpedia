-- Prove2me | solution 1 for NestedLogitVariants.PartialCompetitive.knapsack_relaxation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:32:44.18616+00:00
-- url     : https://prove2.me/submissions/3207bb12-9353-4a38-913c-571c9303ec01

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

set_option autoImplicit false

open NestedLogitVariants.PartialCompetitive in
theorem kr7538_indicator_sum {n : ℕ} (f : Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ j, f j * (if j ∈ S then (1 : ℝ) else 0) = ∑ j ∈ S, f j := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

open NestedLogitVariants.PartialCompetitive in
theorem kr7538_feas {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing) (i : ι) (ε : ℝ)
    (S : Finset (Fin n)) (hS : ∑ j ∈ S, I.v i j ≤ ε) :
    feas11 I i ε (fun j => if j ∈ S then 1 else 0) := by
  refine ⟨?_, ?_⟩
  · rw [kr7538_indicator_sum]; exact hS
  · intro j
    by_cases hj : j ∈ S
    · have h1 : I.v i j ≤ ∑ k ∈ S, I.v i k :=
        Finset.single_le_sum (f := fun k => I.v i k) (fun k _ => (hI.v_pos i k).le) hj
      have h2 : I.v i j ≤ ε := h1.trans hS
      simp [hj, h2]
    · simp only [hj, if_false, le_refl, true_and]
      split_ifs <;> norm_num

open NestedLogitVariants.PartialCompetitive in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (i : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    (∀ S : Finset (Fin n), ∑ j ∈ S, I.v i j ≤ ε →
      feas11 I i ε (fun j => if j ∈ S then 1 else 0)) ∧
    ∃ z : Fin n → ℝ, feas11 I i ε z ∧ Kval I i ε ≤ ∑ j, I.r i j * I.v i j * z j := by
  refine ⟨fun S hS => kr7538_feas I hI i ε S hS, ?_⟩
  have hne : (knapFeasible I i ε).Nonempty := ⟨∅, by simp [knapFeasible, hε]⟩
  obtain ⟨S, hSmem, hSeq⟩ :=
    Finset.exists_mem_eq_sup' hne (fun S => ∑ j ∈ S, I.r i j * I.v i j)
  have hS : ∑ j ∈ S, I.v i j ≤ ε := by
    simp only [knapFeasible, Finset.mem_filter] at hSmem
    exact hSmem.2
  refine ⟨fun j => if j ∈ S then 1 else 0, kr7538_feas I hI i ε S hS, ?_⟩
  rw [kr7538_indicator_sum (fun j => I.r i j * I.v i j) S]
  unfold Kval
  rw [dif_pos hε]
  exact le_of_eq hSeq
