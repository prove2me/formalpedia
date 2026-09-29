-- Prove2me | solution 1 for LassoDantzig.Dantzig.lemma_B3_eq_B9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:10:13.183677+00:00
-- url     : https://prove2.me/submissions/9f46ed7d-c1ab-4ad6-8a07-2f6c30cea2e9

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

open LassoDantzig.Dantzig

theorem solution {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β βD : Fin M → ℝ) (hβ : DantzigConstraint X y r β)
    (hD : IsDantzigSelector X y r βD) :
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
