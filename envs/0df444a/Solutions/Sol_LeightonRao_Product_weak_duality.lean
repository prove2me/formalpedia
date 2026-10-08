-- Prove2me | solution 1 for LeightonRao.Product.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:42:29.569152+00:00
-- url     : https://prove2.me/submissions/02ccdd63-a0b7-4966-953d-0c2a4f223e97

import Mathlib
import Definitions.Def_LeightonRao_Product_Setting
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

private lemma swap4 {V : Type} [Fintype V] [DecidableEq V]
    (A B C D : Finset V) (g : V → V → V → V → ℝ) :
    (∑ s ∈ A, ∑ t ∈ B, ∑ i ∈ C, ∑ j ∈ D, g s t i j) =
      ∑ i ∈ C, ∑ j ∈ D, ∑ s ∈ A, ∑ t ∈ B, g s t i j := by
  calc
    _ = ∑ s ∈ A, ∑ i ∈ C, ∑ t ∈ B, ∑ j ∈ D, g s t i j := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm
    _ = ∑ i ∈ C, ∑ s ∈ A, ∑ t ∈ B, ∑ j ∈ D, g s t i j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = ∑ s ∈ A, ∑ j ∈ D, ∑ t ∈ B, g s t i j := by
          apply Finset.sum_congr rfl
          intro s hs
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

private lemma restrict2 {V : Type} [Fintype V] [DecidableEq V]
    (A B : Finset V) (g : V → V → ℝ) (hg : ∀ s t, 0 ≤ g s t) :
    (∑ s ∈ A, ∑ t ∈ B, g s t) ≤ ∑ s, ∑ t, g s t := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    (fun s hs hsn => Finset.sum_nonneg fun t ht => hg s t)).trans
    (Finset.sum_le_sum fun s hs =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        (fun t ht htn => hg s t))

private lemma undirected_bound {V : Type} [Fintype V] [DecidableEq V]
    (C D : V → V → ℝ) (f : V → V → V → V → ℝ) (lam : ℝ)
    (hn : ∀ s t i j, 0 ≤ f s t i j)
    (hf : ∀ s t, s ≠ t → ∀ v, (∑ j, f s t v j) - (∑ j, f s t j v) =
      lam * D s t * ((if v = s then 1 else 0) - (if v = t then 1 else 0)))
    (hc : ∀ i j, ∑ s, ∑ t, (f s t i j + f s t j i) ≤ C i j)
    (U : Finset V) :
    (∑ s ∈ U, ∑ t ∈ Uᶜ, lam * (D s t + D t s)) ≤
      ∑ i ∈ U, ∑ j ∈ Uᶜ, C i j := by
  classical
  have hb : ∀ s ∈ U, ∀ t ∈ Uᶜ, lam * (D s t + D t s) ≤
      ∑ i ∈ U, ∑ j ∈ Uᶜ, (f s t i j + f t s j i) := by
    intro s hs t ht
    have htn : t ∉ U := Finset.mem_compl.mp ht
    have hst : s ≠ t := by aesop
    have hts : t ≠ s := hst.symm
    have h1 := cut_balance U (f s t)
    have h2 := cut_balance U (f t s)
    have e1 : (∑ v ∈ U, ((∑ j : V, f s t v j) - (∑ j : V, f s t j v))) = lam * D s t := by
      simp_rw [hf s t hst]
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib]
      simp [hs, htn]
    have e2 : (∑ v ∈ U, ((∑ j : V, f t s v j) - (∑ j : V, f t s j v))) = -(lam * D t s) := by
      simp_rw [hf t s hts]
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib]
      simp [hs, htn]
    have n1 : 0 ≤ ∑ i ∈ U, ∑ j ∈ Uᶜ, f s t j i :=
      Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => hn s t j i
    have n2 : 0 ≤ ∑ i ∈ U, ∑ j ∈ Uᶜ, f t s i j :=
      Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => hn t s i j
    simp_rw [Finset.sum_add_distrib]
    nlinarith
  have ht := Finset.sum_le_sum (s := U) fun s hs =>
    Finset.sum_le_sum (s := Uᶜ) fun t ht => hb s hs t ht
  rw [swap4] at ht
  apply ht.trans
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  simp_rw [Finset.sum_add_distrib]
  have h1 := restrict2 U Uᶜ (fun s t => f s t i j) (fun s t => hn s t i j)
  have h2 := restrict2 U Uᶜ (fun s t => f t s j i) (fun s t => hn t s j i)
  have hh : (∑ s, ∑ t, f t s j i) = ∑ s, ∑ t, f s t j i := Finset.sum_comm
  have h3 := hc i j
  simp_rw [Finset.sum_add_distrib] at h3
  rw [hh] at h2
  linarith


open LeightonRao.Product
theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (π : V → ℝ)
    (f : V → V → V → V → ℝ) (lam : ℝ) (hf : IsConcurrentFlow N (productDemand π) f lam)
    (U : Finset V) (hU : 0 < piSum π U) (hUc : 0 < piSum π Uᶜ) :
    lam * (piSum π U * piSum π Uᶜ) ≤ cutCap N U := by
  classical
  have ht := undirected_bound N.C (productDemand π) f lam hf.1 hf.2.1 hf.2.2.2 U
  have he : (∑ s ∈ U, ∑ t ∈ Uᶜ, lam * (productDemand π s t + productDemand π t s)) =
      lam * (piSum π U * piSum π Uᶜ) := by
    have hh : ∀ s ∈ U, ∀ t ∈ Uᶜ, productDemand π s t + productDemand π t s = π s * π t := by
      intro s hs t ht
      have hst : s ≠ t := by
        intro h
        exact (Finset.mem_compl.mp ht) (h ▸ hs)
      simp only [productDemand, if_neg hst, if_neg hst.symm]
      ring
    calc
      _ = ∑ s ∈ U, ∑ t ∈ Uᶜ, lam * (π s * π t) := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro t ht
        rw [hh s hs t ht]
      _ = _ := by
        simp only [piSum, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
  rw [he] at ht
  exact ht

#print axioms solution
