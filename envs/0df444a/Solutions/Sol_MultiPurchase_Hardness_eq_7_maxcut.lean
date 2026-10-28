-- Prove2me | solution 1 for MultiPurchase.Hardness.eq_7_maxcut
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:26:39.196303+00:00
-- url     : https://prove2.me/submissions/64931dc4-64f7-4780-a5d4-b34ce0cf673c

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace Aux_MultiPurchase_Hardness_eq_7_maxcut
open MultiPurchase.Hardness ProjSchedTW.Complexity

theorem symm_split {n : ℕ} (T : Fin n → Fin n → ℚ) (hT : ∀ i j, T i j = T j i) :
    ∑ i, ∑ j, T i j = ∑ i, T i i + 2 * ∑ i, ∑ j, if i < j then T i j else 0 := by
  have h1 : ∀ i j, T i j = (if j = i then T i j else 0) + (if i < j then T i j else 0) +
      (if j < i then T i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_gt h, not_lt_of_gt h]
    · subst h; simp
    · simp [h, ne_of_lt h, not_lt_of_gt h]
  have h2 : ∀ i, ∑ j, T i j = T i i + (∑ j, if i < j then T i j else 0) +
      ∑ j, if j < i then T i j else 0 := by
    intro i
    rw [Finset.sum_congr rfl fun j _ => h1 i j, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq']
    simp
  have h3 : ∑ i, ∑ j, (if j < i then T i j else 0) = ∑ i, ∑ j, (if i < j then T i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [hT]
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib, Finset.sum_add_distrib, h3]
  ring

theorem xC_01 {n : ℕ} (C : Finset (Fin n)) (i : Fin n) : xC C i = 0 ∨ xC C i = 1 := by
  unfold xC; split_ifs <;> simp

noncomputable def val {m : ℕ} (G : SimpleGraph (Fin m)) (C : Finset (Fin (m + 1))) : ℚ :=
  ∑ i, ∑ j, hubQ G i j * xC C i * xC C j

open Classical in
noncomputable def adjQ {m : ℕ} (G : SimpleGraph (Fin m)) (i j : Fin m) : ℚ :=
  if G.Adj i j then 1 else 0

theorem val_eq {m : ℕ} (G : SimpleGraph (Fin m)) (C : Finset (Fin (m + 1))) :
    val G C = xC C 0 * ∑ j, (nodeDeg G j : ℚ) * xC C j.succ -
      ∑ i, ∑ j, adjQ G i j * xC C i.succ * xC C j.succ := by
  classical
  unfold val
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, hubQ, Fin.cases_zero, Fin.cases_succ]
  have e1 : ∀ i : Fin m, (∑ j : Fin m, (if G.Adj i j then (-1 : ℚ) else 0) * xC C i.succ *
      xC C j.succ) = -∑ j, adjQ G i j * xC C i.succ * xC C j.succ := by
    intro i
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold adjQ
    split_ifs <;> ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [Finset.mul_sum]
  have e2 : ∑ x : Fin m, (nodeDeg G x : ℚ) / 2 * xC C 0 * xC C x.succ +
      ∑ x : Fin m, (nodeDeg G x : ℚ) / 2 * xC C x.succ * xC C 0 =
      ∑ i : Fin m, xC C 0 * ((nodeDeg G i : ℚ) * xC C i.succ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith [e2]

theorem nodes_mem {m : ℕ} (C : Finset (Fin (m + 1))) (j : Fin m) :
    j ∈ nodesOf C ↔ j.succ ∈ C := by
  simp [nodesOf]

theorem xC_nodes {m : ℕ} (C : Finset (Fin (m + 1))) (j : Fin m) :
    xC (nodesOf C) j = xC C j.succ := by
  unfold xC
  simp only [nodes_mem]

theorem deg_eq {m : ℕ} (G : SimpleGraph (Fin m)) (j : Fin m) :
    (nodeDeg G j : ℚ) = ∑ k, adjQ G j k := by
  classical
  unfold nodeDeg adjQ
  rw [Finset.card_filter]
  push_cast
  rfl

theorem cut_eq {m : ℕ} (G : SimpleGraph (Fin m)) (A : Finset (Fin m)) :
    (cutSize G A : ℚ) = ∑ a, ∑ b, adjQ G a b * xC A a * (1 - xC A b) := by
  classical
  -- symmetric kernel
  set T : Fin m → Fin m → ℚ := fun a b =>
    adjQ G a b * (xC A a * (1 - xC A b) + xC A b * (1 - xC A a)) with hTdef
  have hadj : ∀ a b, adjQ G a b = adjQ G b a := by
    intro a b; unfold adjQ; simp only [G.adj_comm]
  have hT : ∀ a b, T a b = T b a := by
    intro a b; simp only [hTdef, hadj a b]; ring
  have hdiag : ∀ a, T a a = 0 := by
    intro a; simp [hTdef, adjQ]
  have hsplit := symm_split T hT
  simp only [hdiag, Finset.sum_const_zero, zero_add] at hsplit
  have hfull : ∑ a, ∑ b, T a b = 2 * ∑ a, ∑ b, adjQ G a b * xC A a * (1 - xC A b) := by
    have : ∑ a, ∑ b, T a b = ∑ a, ∑ b, adjQ G a b * xC A a * (1 - xC A b) +
        ∑ a, ∑ b, adjQ G a b * xC A b * (1 - xC A a) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hTdef]; ring
    rw [this]
    have h2 : ∑ a, ∑ b, adjQ G a b * xC A b * (1 - xC A a) =
        ∑ a, ∑ b, adjQ G a b * xC A a * (1 - xC A b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hadj]
    rw [h2]; ring
  have hcut : (cutSize G A : ℚ) = ∑ a, ∑ b, if a < b then T a b else 0 := by
    unfold cutSize
    rw [Finset.card_filter, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hTdef, adjQ, xC]
    by_cases hab : a < b
    · by_cases hadjab : G.Adj a b
      · by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [hab, hadjab, ha, hb]
      · simp [hab, hadjab]
    · simp [hab]
  rw [hcut]
  linarith

end Aux_MultiPurchase_Hardness_eq_7_maxcut

open MultiPurchase.Hardness ProjSchedTW.Complexity Aux_MultiPurchase_Hardness_eq_7_maxcut in
theorem solution {m : ℕ} (G : SimpleGraph (Fin m)) :
    (∀ C : Finset (Fin (m + 1)),
      ∑ i, ∑ j, hubQ G i j * xC C i * xC C j ≤
        ∑ i, ∑ j, hubQ G i j * xC (insert 0 C) i * xC (insert 0 C) j) ∧
    (∀ C : Finset (Fin (m + 1)), 0 ∈ C →
      ∑ i, ∑ j, hubQ G i j * xC C i * xC C j = (cutSize G (nodesOf C) : ℚ)) ∧
    (∀ M : ℕ, (∃ C : Finset (Fin (m + 1)), (M : ℚ) ≤ ∑ i, ∑ j, hubQ G i j * xC C i * xC C j) ↔
      MaxCutYes G M) := by
  have hins : ∀ (C : Finset (Fin (m + 1))) (j : Fin m), xC (insert 0 C) j.succ = xC C j.succ := by
    intro C j
    unfold xC
    simp [Fin.succ_ne_zero]
  have hins0 : ∀ C : Finset (Fin (m + 1)), xC (insert 0 C) 0 = 1 := by
    intro C; simp [xC]
  have P1 : ∀ C : Finset (Fin (m + 1)), val G C ≤ val G (insert 0 C) := by
    intro C
    rw [val_eq, val_eq, hins0]
    simp only [hins]
    have hnn : 0 ≤ ∑ j, (nodeDeg G j : ℚ) * xC C j.succ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
        (by rcases xC_01 C j.succ with h | h <;> rw [h] <;> norm_num)
    have hx : xC C 0 ≤ 1 := by rcases xC_01 C 0 with h | h <;> rw [h] <;> norm_num
    nlinarith
  have P2 : ∀ C : Finset (Fin (m + 1)), 0 ∈ C → val G C = (cutSize G (nodesOf C) : ℚ) := by
    intro C h0
    rw [val_eq, cut_eq]
    have hx0 : xC C 0 = 1 := by simp [xC, h0]
    rw [hx0, one_mul]
    simp only [xC_nodes, deg_eq, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  refine ⟨P1, P2, ?_⟩
  intro M
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨nodesOf (insert 0 C), ?_⟩
    have := P2 (insert 0 C) (Finset.mem_insert_self _ _)
    have h2 : (M : ℚ) ≤ (cutSize G (nodesOf (insert 0 C)) : ℚ) := by
      rw [← this]; exact hC.trans (P1 C)
    exact_mod_cast h2
  · rintro ⟨A, hA⟩
    refine ⟨insert 0 (A.map (Fin.succEmb m)), ?_⟩
    have hN : nodesOf (insert 0 (A.map (Fin.succEmb m))) = A := by
      ext j
      rw [nodes_mem]
      simp [Fin.succ_ne_zero]
    show (M : ℚ) ≤ val G _
    rw [P2 _ (Finset.mem_insert_self _ _), hN]
    exact_mod_cast hA
