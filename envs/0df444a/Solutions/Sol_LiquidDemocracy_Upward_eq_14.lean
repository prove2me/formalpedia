-- Prove2me | solution 1 for LiquidDemocracy.Upward.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:03:12.167385+00:00
-- url     : https://prove2.me/submissions/48003d7d-104e-4f5a-82b9-8db282401c52

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting

namespace Aux_LiquidDemocracy_eq_14
open LiquidDemocracy.Upward
open scoped Classical

theorem union_bound {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (E F H : (Fin n → Bool) → Prop) (h : ∀ v, E v → F v ∨ H v) :
    voteProb c E ≤ voteProb c F + voteProb c H := by
  unfold voteProb
  have hw : ∀ v : Fin n → Bool, 0 ≤ ∏ i, (if v i then c i else 1 - c i) := fun v =>
    Finset.prod_nonneg fun i _ => by split_ifs <;> linarith [(hc i).1, (hc i).2]
  have hsub : Finset.univ.filter E ⊆ Finset.univ.filter F ∪ Finset.univ.filter H := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hv ⊢
    exact h v hv
  calc _ ≤ ∑ v ∈ Finset.univ.filter F ∪ Finset.univ.filter H,
        ∏ i, (if v i then c i else 1 - c i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hw v)
    _ ≤ _ := by
        rw [← Finset.sum_union_inter]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun v _ => hw v)

end Aux_LiquidDemocracy_eq_14

open LiquidDemocracy.Upward in
theorem solution (n : ℕ) (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) (g : DelegGraph n) :
    -voteProb c (fun v => XF g v < XD v) ≤ gain c g := by
  have := Aux_LiquidDemocracy_eq_14.union_bound c hc
    (fun v => (n : ℝ) / 2 < XD v) (fun v => (n : ℝ) / 2 < XF g v) (fun v => XF g v < XD v)
    (by
      intro v hv
      by_cases h : XF g v < XD v
      · exact Or.inr h
      · left; linarith [not_lt.mp h])
  unfold gain
  linarith
