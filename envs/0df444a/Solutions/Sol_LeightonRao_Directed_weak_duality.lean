-- Prove2me | solution 1 for LeightonRao.Directed.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:39:43.55983+00:00
-- url     : https://prove2.me/submissions/c219608f-9e71-4b45-842e-c57d908d05fd

import Definitions.Def_LeightonRao_Directed_Setting
open scoped BigOperators

private lemma split_sum {V : Type} [Fintype V] [DecidableEq V]
    (U : Finset V) (g : V → ℝ) :
    (∑ v ∈ U, g v) + (∑ v ∈ Uᶜ, g v) = ∑ v, g v := by
  have hd : Disjoint U Uᶜ := Finset.disjoint_left.mpr (by
    intro a ha hb
    exact (Finset.mem_compl.mp hb) ha)
  simpa using (Finset.sum_union hd (f := g)).symm

private lemma cut_balance {V : Type} [Fintype V] [DecidableEq V]
    (U : Finset V) (g : V → V → ℝ) :
    (∑ v ∈ U, ((∑ j : V, g v j) - (∑ j : V, g j v))) =
      (∑ i ∈ U, ∑ j ∈ Uᶜ, g i j) - (∑ i ∈ U, ∑ j ∈ Uᶜ, g j i) := by
  simp_rw [← split_sum U]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hc : (∑ i ∈ U, ∑ j ∈ U, g i j) = ∑ i ∈ U, ∑ j ∈ U, g j i :=
    Finset.sum_comm
  linarith

open LeightonRao.Directed
theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (f : V → V → V → V → ℝ) (lam : ℝ) (hf : IsDiConcurrentFlow N diDemand f lam)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty) :
    lam * ((U.card : ℝ) * (Uᶜ.card : ℝ)) ≤ diCutCap N U := by
  classical
  have hb : ∀ s ∈ U, ∀ t ∈ Uᶜ, lam ≤ ∑ i ∈ U, ∑ j ∈ Uᶜ, f s t i j := by
    intro s hs t ht
    have htn : t ∉ U := Finset.mem_compl.mp ht
    have hst : s ≠ t := by aesop
    have hh := cut_balance U (f s t)
    have he : (∑ v ∈ U, ((∑ j : V, f s t v j) - (∑ j : V, f s t j v))) = lam := by
      simp_rw [hf.2.1 s t hst]
      simp only [diDemand, if_neg hst, mul_one, mul_sub]
      rw [Finset.sum_sub_distrib]
      simp [← Finset.mul_sum, hs, htn]
    have hn : 0 ≤ ∑ i ∈ U, ∑ j ∈ Uᶜ, f s t j i :=
      Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => hf.1 s t j i
    linarith
  have ht := Finset.sum_le_sum (s := U) fun s hs =>
    Finset.sum_le_sum (s := Uᶜ) fun t ht => hb s hs t ht
  have hr : (∑ s ∈ U, ∑ t ∈ Uᶜ, ∑ i ∈ U, ∑ j ∈ Uᶜ, f s t i j) =
      ∑ i ∈ U, ∑ j ∈ Uᶜ, ∑ s ∈ U, ∑ t ∈ Uᶜ, f s t i j := by
    calc
      _ = ∑ s ∈ U, ∑ i ∈ U, ∑ t ∈ Uᶜ, ∑ j ∈ Uᶜ, f s t i j := by
        apply Finset.sum_congr rfl
        intro s hs
        exact Finset.sum_comm
      _ = ∑ i ∈ U, ∑ s ∈ U, ∑ t ∈ Uᶜ, ∑ j ∈ Uᶜ, f s t i j := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∑ s ∈ U, ∑ j ∈ Uᶜ, ∑ t ∈ Uᶜ, f s t i j := by
            apply Finset.sum_congr rfl
            intro s hs
            exact Finset.sum_comm
          _ = _ := Finset.sum_comm
  have hc : (∑ i ∈ U, ∑ j ∈ Uᶜ, ∑ s ∈ U, ∑ t ∈ Uᶜ, f s t i j) ≤ diCutCap N U := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
        (fun s hs hsn => Finset.sum_nonneg fun t ht => hf.1 s t i j) |>.trans
        (Finset.sum_le_sum fun s hs =>
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Uᶜ)
            (fun t ht htn => hf.1 s t i j)))
      (hf.2.2.2 i j)
  rw [hr] at ht
  simpa [mul_assoc, mul_comm, mul_left_comm] using ht.trans hc

#print axioms solution
