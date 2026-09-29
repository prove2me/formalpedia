-- Prove2me | solution 1 for LassoDantzig.Equivalence.lemma_B3_eq_B9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:10:14.174254+00:00
-- url     : https://prove2.me/submissions/210b44f0-763d-4ea0-8ad4-4ca017fad2c7

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

open LassoDantzig.Equivalence

theorem solution {n M : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (β βD : Fin M → ℝ) (hβ : DantzigFeasible X y r β) (hD : IsDantzig X y r βD) :
    l1On (βD - β) (supp β)ᶜ ≤ l1On (βD - β) (supp β) := by
  have hmin := hD.2 β hβ
  have hzero : ∀ j ∈ (supp β)ᶜ, β j = 0 := by
    intro j hj
    simp only [supp, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_not] at hj
    exact hj
  have hsplitD : ∑ j, |βD j| = ∑ j ∈ supp β, |βD j| + ∑ j ∈ (supp β)ᶜ, |βD j| :=
    (Finset.sum_add_sum_compl (supp β) (fun j => |βD j|)).symm
  have hzc : ∑ j ∈ (supp β)ᶜ, |β j| = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hzero j hj, abs_zero]
  have hsplitB : ∑ j, |β j| = ∑ j ∈ supp β, |β j| := by
    rw [← Finset.sum_add_sum_compl (supp β) (fun j => |β j|), hzc, add_zero]
  have hc : ∑ j ∈ (supp β)ᶜ, |βD j| = l1On (βD - β) (supp β)ᶜ := by
    unfold l1On
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Pi.sub_apply, hzero j hj, sub_zero]
  have hJ : ∑ j ∈ supp β, |β j| - l1On (βD - β) (supp β) ≤ ∑ j ∈ supp β, |βD j| := by
    unfold l1On
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hab := abs_sub_abs_le_abs_sub (β j) (βD j)
    rw [abs_sub_comm] at hab
    simp only [Pi.sub_apply]
    linarith
  rw [hsplitD, hc, hsplitB] at hmin
  linarith
