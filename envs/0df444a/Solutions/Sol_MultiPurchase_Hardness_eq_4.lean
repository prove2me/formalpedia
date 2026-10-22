-- Prove2me | solution 1 for MultiPurchase.Hardness.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:46:29.925298+00:00
-- url     : https://prove2.me/submissions/a5027ab0-7208-467e-bea5-62e6452aba7d

import Mathlib
import Definitions.Def_MultiPurchase_Hardness_Model
set_option autoImplicit false

open MultiPurchase.Hardness

lemma aaa_row {n : ℕ} (C : Finset (Fin n)) (g : Fin n → Fin n → ℚ) (i : Fin n) (hi : i ∈ C) :
    ∑ j ∈ C, g i j = g i i + ∑ j ∈ C.filter (fun j => i < j), g i j
      + ∑ j ∈ C.filter (fun j => j < i), g i j := by
  rw [← Finset.sum_filter_add_sum_filter_not C (fun j => i < j)]
  rw [← Finset.sum_filter_add_sum_filter_not (C.filter (fun j => ¬ i < j)) (fun j => j < i)]
  have h1 : (C.filter (fun j => ¬ i < j)).filter (fun j => j < i) = C.filter (fun j => j < i) := by
    ext j; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
    · rintro ⟨a, c⟩; exact ⟨⟨a, not_lt_of_gt c⟩, c⟩
  have h2 : (C.filter (fun j => ¬ i < j)).filter (fun j => ¬ j < i) = {i} := by
    ext j; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact le_antisymm (not_lt.1 b) (not_lt.1 c)
    · rintro rfl; exact ⟨⟨hi, lt_irrefl _⟩, lt_irrefl _⟩
  rw [h1, h2, Finset.sum_singleton]
  ring

lemma aaa_split {n : ℕ} (C : Finset (Fin n)) (g : Fin n → Fin n → ℚ) :
    ∑ i ∈ C, ∑ j ∈ C, g i j = ∑ i ∈ C, g i i
      + ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), (g i j + g j i) := by
  have h : ∑ i ∈ C, ∑ j ∈ C, g i j = ∑ i ∈ C, (g i i + ∑ j ∈ C.filter (fun j => i < j), g i j
      + ∑ j ∈ C.filter (fun j => j < i), g i j) :=
    Finset.sum_congr rfl (fun i hi => aaa_row C g i hi)
  rw [h, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h3 : ∑ i ∈ C, ∑ j ∈ C.filter (fun j => j < i), g i j
      = ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), g j i := by
    refine Finset.sum_comm' ?_
    intro x y
    simp only [Finset.mem_filter]
    tauto
  simp only [Finset.sum_add_distrib]
  rw [h3]
  ring

lemma aaa_ind {n : ℕ} (C : Finset (Fin n)) (g : Fin n → Fin n → ℚ) :
    ∑ i, ∑ j, g i j * xC C i * xC C j = ∑ i ∈ C, ∑ j ∈ C, g i j := by
  unfold xC
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ C)]
  have hC : Finset.univ.filter (fun i => i ∈ C) = C := by ext; simp
  rw [hC]
  have h0 : ∑ i ∈ Finset.univ.filter (fun i => i ∉ C), ∑ j, g i j * (if i ∈ C then (1:ℚ) else 0)
      * (if j ∈ C then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp [hi.2]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ C), hC]
  have h1 : ∑ j ∈ Finset.univ.filter (fun j => j ∉ C), g i j * (if i ∈ C then (1:ℚ) else 0)
      * (if j ∈ C then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter] at hj
    simp [hj.2]
  rw [h1, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp [hi, hj]

theorem solution (I : Instance) (C : Finset (Fin I.n)) :
    I.R2 C = (∑ i, ∑ j, I.rhat i j * I.theta i j * xC C i * xC C j) /
      (I.v0 + ∑ i, ∑ j, I.theta i j * xC C i * xC C j) := by
  unfold Instance.R2
  rw [aaa_ind C (fun i j => I.rhat i j * I.theta i j), aaa_ind C (fun i j => I.theta i j),
    aaa_split C, aaa_split C]
  have key1 : ∀ i ∈ C, I.rhat i i * I.theta i i = I.r i * I.V1 i := by
    intro i _; simp [Instance.rhat, Instance.theta]
  have key2 : ∀ i j, i < j → I.rhat i j * I.theta i j + I.rhat j i * I.theta j i
      = (I.r i + I.r j) * I.V2 i j := by
    intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    have hne' : j ≠ i := ne_of_gt hij
    simp only [Instance.rhat, Instance.theta, hne, hne', if_false, min_eq_left hij.le,
      max_eq_right hij.le, min_eq_right hij.le, max_eq_left hij.le]
    ring
  have key3 : ∀ i j, i < j → I.theta i j + I.theta j i = I.V2 i j := by
    intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    have hne' : j ≠ i := ne_of_gt hij
    simp only [Instance.theta, hne, hne', if_false, min_eq_left hij.le,
      max_eq_right hij.le, min_eq_right hij.le, max_eq_left hij.le]
    ring
  have e1 : ∑ i ∈ C, I.rhat i i * I.theta i i = ∑ i ∈ C, I.r i * I.V1 i :=
    Finset.sum_congr rfl key1
  have e2 : ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j),
        (I.rhat i j * I.theta i j + I.rhat j i * I.theta j i)
      = ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), (I.r i + I.r j) * I.V2 i j := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j hj
    exact key2 i j (Finset.mem_filter.1 hj).2
  have e3 : ∑ i ∈ C, I.theta i i = ∑ i ∈ C, I.V1 i :=
    Finset.sum_congr rfl (fun i _ => by simp [Instance.theta])
  have e4 : ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), (I.theta i j + I.theta j i)
      = ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), I.V2 i j := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j hj
    exact key3 i j (Finset.mem_filter.1 hj).2
  rw [e1, e2, e3, e4]
  ring_nf
