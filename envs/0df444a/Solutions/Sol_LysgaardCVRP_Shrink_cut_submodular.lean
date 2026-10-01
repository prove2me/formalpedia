-- Prove2me | solution 1 for LysgaardCVRP.Shrink.cut_submodular
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:32:15.858985+00:00
-- url     : https://prove2.me/submissions/98b70f0c-1f97-45d3-a914-15a0fb6fb233

import Definitions.Def_LysgaardCVRP_Shrink_cut
import Mathlib.Tactic
open scoped BigOperators
open LysgaardCVRP.Shrink

private lemma cut_formula {n : ℕ} (x : Sym2 (Fin (n+1)) → ℝ)
    (S : Finset (Fin (n+1))) :
    cut x S = ∑ i, ∑ j, if i ∈ S ∧ j ∉ S then x s(i,j) else 0 := by
  classical
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    ← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hc : (Finset.univ.filter (fun i => i ∉ S)) = Sᶜ := by ext i; simp
  rw [hc]
  rfl

theorem solution {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S T : Finset (Fin (n + 1))) :
    cut x T - cut x (S ∪ T) ≥ cut x (S ∩ T) - cut x S := by
  classical
  have h : cut x (S ∩ T) + cut x (S ∪ T) ≤ cut x S + cut x T := by
    simp only [cut_formula, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    by_cases his : i ∈ S <;> by_cases hit : i ∈ T <;>
      by_cases hjs : j ∈ S <;> by_cases hjt : j ∈ T <;>
      simp [his, hit, hjs, hjt, hx]
  linarith
