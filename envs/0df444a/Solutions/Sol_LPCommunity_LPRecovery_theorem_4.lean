-- Prove2me | solution 1 for LPCommunity.LPRecovery.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T21:53:04.087805+00:00
-- url     : https://prove2.me/submissions/921eb97d-e481-4f7b-8b02-0a414ff04471

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting

set_option autoImplicit false

open Finset
open scoped Classical

namespace LPR4

open LPCommunity.MinBisect LPCommunity.LPRecovery

lemma sum_ite_const' {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (c : ℝ) :
    (∑ j, if p j then c else 0) = ((univ.filter p).card : ℝ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

lemma two_sum_lt {n : ℕ} (f : Fin n → Fin n → ℝ) (hs : ∀ i j, f i j = f j i)
    (hd : ∀ i, f i i = 0) :
    2 * (∑ i, ∑ j, if i < j then f i j else 0) = ∑ i, ∑ j, f i j := by
  have h1 : (∑ i, ∑ j, f i j) = (∑ i, ∑ j, if i < j then f i j else 0) +
      ∑ i, ∑ j, if j < i then f i j else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [hd]
    · simp [h, not_lt.mpr h.le]
  have h2 : (∑ i, ∑ j, if j < i then f i j else 0) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hs]
  rw [h1, h2]; ring

lemma ss_refl {n : ℕ} (V1 : Finset (Fin n)) (i : Fin n) : sameSide V1 i i := Iff.rfl

lemma ss_symm {n : ℕ} {V1 : Finset (Fin n)} {i j : Fin n} (h : sameSide V1 i j) :
    sameSide V1 j i := Iff.symm h

lemma ss_symm_iff {n : ℕ} (V1 : Finset (Fin n)) (i j : Fin n) :
    sameSide V1 i j ↔ sameSide V1 j i := ⟨ss_symm, ss_symm⟩

lemma ss_trans {n : ℕ} {V1 : Finset (Fin n)} {i j k : Fin n} (h1 : sameSide V1 i j)
    (h2 : sameSide V1 j k) : sameSide V1 i k := Iff.trans h1 h2

lemma ss_of_nn {n : ℕ} {V1 : Finset (Fin n)} {i j k : Fin n} (h1 : ¬ sameSide V1 i k)
    (h2 : ¬ sameSide V1 j k) : sameSide V1 i j := by
  unfold sameSide at *; tauto

lemma nss_of {n : ℕ} {V1 : Finset (Fin n)} {i j k : Fin n} (h1 : sameSide V1 i j)
    (h2 : ¬ sameSide V1 j k) : ¬ sameSide V1 i k := fun h => h2 (ss_trans (ss_symm h1) h)

lemma card_same {n : ℕ} (V1 : Finset (Fin n)) (hV1 : IsBisection n V1) (i : Fin n) :
    ((univ.filter fun j => sameSide V1 i j).card : ℝ) = V1.card := by
  unfold IsBisection at hV1
  by_cases hi : i ∈ V1
  · have : (univ.filter fun j => sameSide V1 i j) = V1 := by
      ext j; simp [sameSide, hi]
    rw [this]
  · have : (univ.filter fun j => sameSide V1 i j) = V1ᶜ := by
      ext j; simp [sameSide, hi]
    rw [this, Finset.card_compl, Fintype.card_fin]
    norm_cast; omega

lemma card_cross {n : ℕ} (V1 : Finset (Fin n)) (hV1 : IsBisection n V1) (i : Fin n) :
    ((univ.filter fun j => ¬ sameSide V1 i j).card : ℝ) = V1.card := by
  unfold IsBisection at hV1
  by_cases hi : i ∈ V1
  · have : (univ.filter fun j => ¬ sameSide V1 i j) = V1ᶜ := by
      ext j; simp [sameSide, hi]
    rw [this, Finset.card_compl, Fintype.card_fin]
    norm_cast; omega
  · have : (univ.filter fun j => ¬ sameSide V1 i j) = V1 := by
      ext j; simp [sameSide, hi]
    rw [this]

section feas

variable {n : ℕ} {x : Fin n → Fin n → ℝ}

lemma tri (hx : LPFeasible n x) {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    x i j ≤ x i k + x k j := by
  obtain ⟨hs, _, h1, _, _⟩ := hx
  have e1 := hs i j
  have e2 := hs k j
  have e3 := hs i k
  rcases lt_or_gt_of_ne hij with h | h
  · have := h1 i j k h hki hkj; linarith
  · have := h1 j i k h hkj hki; linarith

lemma perim (hx : LPFeasible n x) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    x i j + x i k + x j k ≤ 2 := by
  obtain ⟨hs, _, _, h2, _⟩ := hx
  have e1 := hs i j
  have e2 := hs i k
  have e3 := hs j k
  rcases lt_or_gt_of_ne hij with a | a <;> rcases lt_or_gt_of_ne hik with b | b <;>
    rcases lt_or_gt_of_ne hjk with c | c
  all_goals first
    | linarith [h2 i j k ‹_› ‹_›]
    | linarith [h2 i k j ‹_› ‹_›]
    | linarith [h2 j i k ‹_› ‹_›]
    | linarith [h2 j k i ‹_› ‹_›]
    | linarith [h2 k i j ‹_› ‹_›]
    | linarith [h2 k j i ‹_› ‹_›]

lemma x_nonneg (hx : LPFeasible n x) (h3 : ∀ i j : Fin n, ∃ k, k ≠ i ∧ k ≠ j)
    (i j : Fin n) : 0 ≤ x i j := by
  by_cases hij : i = j
  · subst hij; rw [hx.2.1]
  obtain ⟨k, hki, hkj⟩ := h3 i j
  have t1 := tri hx (i := i) (j := k) (k := j) (Ne.symm hki) (Ne.symm hij) (fun h => hkj h.symm)
  have t2 := tri hx (i := j) (j := k) (k := i) (fun h => hkj h.symm) hij (Ne.symm hki)
  have e := hx.1 i j
  have e2 := hx.1 j k
  have e3 := hx.1 k i
  linarith

lemma x_le_one (hx : LPFeasible n x) (h3 : ∀ i j : Fin n, ∃ k, k ≠ i ∧ k ≠ j)
    (i j : Fin n) : x i j ≤ 1 := by
  by_cases hij : i = j
  · subst hij; rw [hx.2.1]; norm_num
  obtain ⟨k, hki, hkj⟩ := h3 i j
  have t1 := tri hx hij hki hkj
  have p := perim hx hij (Ne.symm hki) (Ne.symm hkj)
  have e := hx.1 k j
  linarith

end feas

/-- Deviation of `x` from the cut vector of `V1`. -/
noncomputable def dev {n : ℕ} (V1 : Finset (Fin n)) (x : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  if sameSide V1 i j then x i j else 1 - x i j

section devs

variable {n : ℕ} {V1 : Finset (Fin n)} {x : Fin n → Fin n → ℝ}

lemma dev_diag (hx : LPFeasible n x) (i : Fin n) : dev V1 x i i = 0 := by
  simp [dev, ss_refl, hx.2.1 i]

lemma dev_nonneg (hx : LPFeasible n x) (h3 : ∀ i j : Fin n, ∃ k, k ≠ i ∧ k ≠ j)
    (i j : Fin n) : 0 ≤ dev V1 x i j := by
  unfold dev
  split_ifs
  · exact x_nonneg hx h3 i j
  · linarith [x_le_one hx h3 i j]

lemma devA (hx : LPFeasible n x) {i j k : Fin n} (hij : sameSide V1 i j)
    (hik : ¬ sameSide V1 i k) : dev V1 x i k ≤ dev V1 x j k + dev V1 x i j := by
  by_cases e : i = j
  · subst e; rw [dev_diag hx]; simp
  have hjk : ¬ sameSide V1 j k := nss_of (ss_symm hij) hik
  have hki : k ≠ i := fun h => hik (h ▸ ss_refl V1 i)
  have hkj : k ≠ j := fun h => hjk (h ▸ ss_refl V1 j)
  simp only [dev, hij, hik, hjk, if_true, if_false]
  have t := tri hx (i := j) (j := k) (k := i) (Ne.symm hkj) e (Ne.symm hki)
  have s1 := hx.1 j i
  linarith

lemma devB (hx : LPFeasible n x) {i j k : Fin n} (hij : sameSide V1 i j)
    (hik : ¬ sameSide V1 i k) (hne : j ≠ i) : dev V1 x i j ≤ dev V1 x i k + dev V1 x j k := by
  have hjk : ¬ sameSide V1 j k := nss_of (ss_symm hij) hik
  have hki : k ≠ i := fun h => hik (h ▸ ss_refl V1 i)
  have hkj : k ≠ j := fun h => hjk (h ▸ ss_refl V1 j)
  simp only [dev, hij, hik, hjk, if_true, if_false]
  have p := perim hx (Ne.symm hne) (Ne.symm hki) (Ne.symm hkj)
  linarith

end devs

lemma sum3_comm {n : ℕ} (F : Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ k, ∑ j, F i k j) = ∑ j, ∑ k, ∑ i, F i k j := by
  calc (∑ i, ∑ k, ∑ j, F i k j) = ∑ k, ∑ i, ∑ j, F i k j := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, F i k j := Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ j, ∑ k, ∑ i, F i k j := Finset.sum_comm

lemma ite_add' {P : Prop} [Decidable P] (a b : ℝ) :
    (if P then a + b else 0) = (if P then a else 0) + (if P then b else 0) := by
  split_ifs <;> simp

/-- Same-side pairs, off-diagonal, not edges of `H1`. -/
def Pn {n : ℕ} (V1 : Finset (Fin n)) (H1 : SimpleGraph (Fin n)) (i j : Fin n) : Prop :=
  sameSide V1 i j ∧ j ≠ i ∧ ¬ H1.Adj i j

section graphs

variable {n : ℕ} {V1 : Finset (Fin n)}

lemma card_H1 (H1 : SimpleGraph (Fin n)) (din : ℕ) (hH1s : ∀ i j, H1.Adj i j → sameSide V1 i j)
    (hH1d : ∀ v, inDeg H1 V1 v = din) (i : Fin n) :
    ((univ.filter fun j => H1.Adj i j).card : ℝ) = din := by
  rw [← hH1d i]
  unfold inDeg
  congr 2
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h, hH1s i j h⟩, fun h => h.1⟩

lemma cardP (hV1 : IsBisection n V1) (H1 : SimpleGraph (Fin n)) (din : ℕ)
    (hH1s : ∀ i j, H1.Adj i j → sameSide V1 i j)
    (hH1d : ∀ v, inDeg H1 V1 v = din) (i : Fin n) :
    ((univ.filter fun j => Pn V1 H1 i j).card : ℝ) = V1.card - 1 - din := by
  have e1 := card_same V1 hV1 i
  have e2 := card_H1 H1 din hH1s hH1d i
  have hsplit : ∀ j, (if sameSide V1 i j then (1:ℝ) else 0) =
      (if j = i then 1 else 0) + (if H1.Adj i j then 1 else 0) + (if Pn V1 H1 i j then 1 else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [Pn, ss_refl]
    · by_cases hh : H1.Adj i j
      · have := hH1s i j hh
        simp [Pn, hj, hh, this]
      · simp [Pn, hj, hh]
  have hs : (∑ j, if sameSide V1 i j then (1:ℝ) else 0) =
      (∑ j, if j = i then (1:ℝ) else 0) + (∑ j, if H1.Adj i j then (1:ℝ) else 0) +
        ∑ j, if Pn V1 H1 i j then (1:ℝ) else 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hsplit j
  have h0 : (∑ j : Fin n, if j = i then (1:ℝ) else 0) = 1 := by simp
  rw [h0, sum_ite_const', sum_ite_const', sum_ite_const', e1, e2] at hs
  linarith

lemma card_H0 (H0 : SimpleGraph (Fin n)) (dout : ℕ) (hH0s : ∀ i j, H0.Adj i j → ¬ sameSide V1 i j)
    (hH0d : ∀ v, outDeg H0 V1 v = dout) (i : Fin n) :
    ((univ.filter fun k => H0.Adj i k).card : ℝ) = dout := by
  rw [← hH0d i]
  unfold outDeg
  congr 2
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h, hH0s i k h⟩, fun h => h.1⟩

lemma card_H0' (H0 : SimpleGraph (Fin n)) (dout : ℕ) (hH0s : ∀ i j, H0.Adj i j → ¬ sameSide V1 i j)
    (hH0d : ∀ v, outDeg H0 V1 v = dout) (j k : Fin n) :
    ((univ.filter fun i => H0.Adj i k ∧ sameSide V1 i j).card : ℝ) =
      if sameSide V1 j k then 0 else dout := by
  by_cases hjk : sameSide V1 j k
  · rw [if_pos hjk]
    have : (univ.filter fun i => H0.Adj i k ∧ sameSide V1 i j) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      intro hik hij
      exact hH0s i k hik (ss_trans hij hjk)
    rw [this]; simp
  · rw [if_neg hjk, ← card_H0 H0 dout hH0s hH0d k]
    congr 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact H0.adj_symm h.1
    · intro h
      have hki := hH0s k i h
      exact ⟨H0.adj_symm h, ss_of_nn (fun h' => hki (ss_symm h')) hjk⟩

end graphs

section bounds

variable {n : ℕ} {V1 : Finset (Fin n)} {x : Fin n → Fin n → ℝ}

lemma Qbound (hV1 : IsBisection n V1) (hx : LPFeasible n x)
    (H0 : SimpleGraph (Fin n)) (dout : ℕ) (hH0s : ∀ i j, H0.Adj i j → ¬ sameSide V1 i j)
    (hH0d : ∀ v, outDeg H0 V1 v = dout) :
    (V1.card : ℝ) * (∑ i, ∑ k, if H0.Adj i k then dev V1 x i k else 0) ≤
      dout * ((∑ i, ∑ j, if sameSide V1 i j then dev V1 x i j else 0) +
        ∑ i, ∑ j, if ¬ sameSide V1 i j then dev V1 x i j else 0) := by
  have step : ∀ i k, (V1.card : ℝ) * (if H0.Adj i k then dev V1 x i k else 0) ≤
      ∑ j, (if H0.Adj i k ∧ sameSide V1 i j then dev V1 x j k + dev V1 x i j else 0) := by
    intro i k
    by_cases hik : H0.Adj i k
    · have hns := hH0s i k hik
      rw [if_pos hik, ← card_same V1 hV1 i, ← sum_ite_const']
      apply Finset.sum_le_sum; intro j _
      by_cases hj : sameSide V1 i j
      · rw [if_pos hj, if_pos ⟨hik, hj⟩]; exact devA hx hj hns
      · rw [if_neg hj, if_neg (fun h => hj h.2)]
    · simp [hik]
  have X2 : ∀ i, (∑ k, ∑ j, if H0.Adj i k ∧ sameSide V1 i j then dev V1 x i j else 0) =
      dout * ∑ j, if sameSide V1 i j then dev V1 x i j else 0 := by
    intro i
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : sameSide V1 i j
    · simp only [hj, and_true, if_true]
      rw [sum_ite_const', card_H0 H0 dout hH0s hH0d i]
    · simp [hj]
  have X1 : (∑ i, ∑ k, ∑ j, if H0.Adj i k ∧ sameSide V1 i j then dev V1 x j k else 0) =
      dout * ∑ j, ∑ k, if ¬ sameSide V1 j k then dev V1 x j k else 0 := by
    rw [sum3_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_ite_const', card_H0' H0 dout hH0s hH0d j k]
    by_cases hjk : sameSide V1 j k <;> simp [hjk]
  calc (V1.card : ℝ) * (∑ i, ∑ k, if H0.Adj i k then dev V1 x i k else 0)
      = ∑ i, ∑ k, (V1.card : ℝ) * (if H0.Adj i k then dev V1 x i k else 0) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, ∑ j, (if H0.Adj i k ∧ sameSide V1 i j then dev V1 x j k + dev V1 x i j
          else 0) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => step i k
    _ = (∑ i, ∑ k, ∑ j, if H0.Adj i k ∧ sameSide V1 i j then dev V1 x j k else 0) +
        ∑ i, ∑ k, ∑ j, if H0.Adj i k ∧ sameSide V1 i j then dev V1 x i j else 0 := by
        simp only [ite_add', Finset.sum_add_distrib]
    _ = _ := by rw [X1, Finset.sum_congr rfl fun i _ => X2 i, ← Finset.mul_sum]; ring

lemma Pn_symm {H1 : SimpleGraph (Fin n)} {i j : Fin n} (h : Pn V1 H1 i j) : Pn V1 H1 j i :=
  ⟨ss_symm h.1, Ne.symm h.2.1, fun h' => h.2.2 (H1.adj_symm h')⟩

lemma Nbound (hV1 : IsBisection n V1) (hx : LPFeasible n x)
    (H1 : SimpleGraph (Fin n)) (din : ℕ) (hH1s : ∀ i j, H1.Adj i j → sameSide V1 i j)
    (hH1d : ∀ v, inDeg H1 V1 v = din) :
    (V1.card : ℝ) * (∑ i, ∑ j, if Pn V1 H1 i j then dev V1 x i j else 0) ≤
      2 * ((V1.card : ℝ) - 1 - din) * ∑ i, ∑ k, if ¬ sameSide V1 i k then dev V1 x i k else 0 := by
  have step : ∀ i j, (V1.card : ℝ) * (if Pn V1 H1 i j then dev V1 x i j else 0) ≤
      ∑ k, (if Pn V1 H1 i j ∧ ¬ sameSide V1 i k then dev V1 x i k + dev V1 x j k else 0) := by
    intro i j
    by_cases hp : Pn V1 H1 i j
    · rw [if_pos hp, ← card_cross V1 hV1 i, ← sum_ite_const']
      apply Finset.sum_le_sum; intro k _
      by_cases hk : ¬ sameSide V1 i k
      · rw [if_pos hk, if_pos ⟨hp, hk⟩]; exact devB hx hp.1 hk hp.2.1
      · rw [if_neg hk, if_neg (fun h => hk h.2)]
    · simp [hp]
  have Y1 : (∑ i, ∑ j, ∑ k, if Pn V1 H1 i j ∧ ¬ sameSide V1 i k then dev V1 x i k else 0) =
      ((V1.card : ℝ) - 1 - din) * ∑ i, ∑ k, if ¬ sameSide V1 i k then dev V1 x i k else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : sameSide V1 i k
    · simp [hk]
    · simp only [hk, not_false_eq_true, and_true, if_true]
      rw [sum_ite_const', cardP hV1 H1 din hH1s hH1d i]
  have Y2 : (∑ i, ∑ j, ∑ k, if Pn V1 H1 i j ∧ ¬ sameSide V1 i k then dev V1 x j k else 0) =
      ∑ i, ∑ j, ∑ k, if Pn V1 H1 i j ∧ ¬ sameSide V1 i k then dev V1 x i k else 0 := by
    calc (∑ i, ∑ j, ∑ k, if Pn V1 H1 i j ∧ ¬ sameSide V1 i k then dev V1 x j k else 0)
        = ∑ i, ∑ j, ∑ k, if Pn V1 H1 j i ∧ ¬ sameSide V1 j k then dev V1 x j k else 0 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => ?_
          have hiff : (Pn V1 H1 i j ∧ ¬ sameSide V1 i k) ↔ (Pn V1 H1 j i ∧ ¬ sameSide V1 j k) :=
            ⟨fun h => ⟨Pn_symm h.1, nss_of (ss_symm h.1.1) h.2⟩,
             fun h => ⟨Pn_symm h.1, nss_of (ss_symm h.1.1) h.2⟩⟩
          by_cases h : Pn V1 H1 i j ∧ ¬ sameSide V1 i k
          · rw [if_pos h, if_pos (hiff.mp h)]
          · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
      _ = _ := Finset.sum_comm
  calc (V1.card : ℝ) * (∑ i, ∑ j, if Pn V1 H1 i j then dev V1 x i j else 0)
      = ∑ i, ∑ j, (V1.card : ℝ) * (if Pn V1 H1 i j then dev V1 x i j else 0) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ∑ k, (if Pn V1 H1 i j ∧ ¬ sameSide V1 i k then dev V1 x i k + dev V1 x j k
          else 0) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => step i j
    _ = (∑ i, ∑ j, ∑ k, if Pn V1 H1 i j ∧ ¬ sameSide V1 i k then dev V1 x i k else 0) +
        ∑ i, ∑ j, ∑ k, if Pn V1 H1 i j ∧ ¬ sameSide V1 i k then dev V1 x j k else 0 := by
        simp only [ite_add', Finset.sum_add_distrib]
    _ = _ := by rw [Y2, Y1]; ring

lemma split_same (hx : LPFeasible n x) (H1 : SimpleGraph (Fin n))
    (hH1s : ∀ i j, H1.Adj i j → sameSide V1 i j) :
    (∑ i, ∑ j, if sameSide V1 i j then dev V1 x i j else 0) =
      (∑ i, ∑ j, if H1.Adj i j then dev V1 x i j else 0) +
        ∑ i, ∑ j, if Pn V1 H1 i j then dev V1 x i j else 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hh : H1.Adj i j
  · have hs := hH1s i j hh
    have hne : j ≠ i := fun e => by subst e; exact H1.loopless.irrefl j hh
    have hp : ¬ Pn V1 H1 i j := fun h => h.2.2 hh
    rw [if_pos hs, if_pos hh, if_neg hp]; ring
  · by_cases hs : sameSide V1 i j
    · by_cases hji : j = i
      · subst hji
        have hp : ¬ Pn V1 H1 j j := fun h => h.2.1 rfl
        rw [if_pos hs, if_neg hh, if_neg hp, dev_diag hx]; ring
      · have hp : Pn V1 H1 i j := ⟨hs, hji, hh⟩
        rw [if_pos hs, if_neg hh, if_pos hp]; ring
    · have hp : ¬ Pn V1 H1 i j := fun h => hs h.1
      rw [if_neg hs, if_neg hh, if_neg hp]; ring

lemma total_dev (i j : Fin n) :
    (if sameSide V1 i j then dev V1 x i j else 0) + (if ¬ sameSide V1 i j then dev V1 x i j else 0)
      = dev V1 x i j := by
  by_cases h : sameSide V1 i j <;> simp [h]

lemma diff_dev (i j : Fin n) :
    x i j - cutVec V1 i j =
      (if sameSide V1 i j then dev V1 x i j else 0) - (if ¬ sameSide V1 i j then dev V1 x i j else 0) := by
  by_cases h : sameSide V1 i j <;> simp [h, dev, cutVec]

end bounds

section cut

variable {n : ℕ}

lemma cut_feasible (V1 : Finset (Fin n)) (hV1 : IsBisection n V1) : LPFeasible n (cutVec V1) := by
  have hsym : ∀ i j, cutVec V1 i j = cutVec V1 j i := by
    intro i j
    unfold cutVec
    by_cases h : sameSide V1 i j
    · rw [if_pos h, if_pos (ss_symm h)]
    · rw [if_neg h, if_neg (fun h' => h (ss_symm h'))]
  have hdiag : ∀ i, cutVec V1 i i = 0 := fun i => by simp [cutVec, ss_refl]
  refine ⟨hsym, hdiag, ?_, ?_, ?_⟩
  · intro i j k _ _ _
    unfold cutVec sameSide
    split_ifs <;> (try norm_num) <;> tauto
  · intro i j k _ _
    unfold cutVec sameSide
    split_ifs <;> (try norm_num) <;> tauto
  · have h := two_sum_lt (cutVec V1) hsym hdiag
    have hrow : ∀ i, (∑ j, cutVec V1 i j) = V1.card := by
      intro i
      have : (∑ j, cutVec V1 i j) = ∑ j, if ¬ sameSide V1 i j then (1:ℝ) else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hs : sameSide V1 i j <;> simp [cutVec, hs]
      rw [this, sum_ite_const', card_cross V1 hV1 i, mul_one]
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    unfold IsBisection at hV1
    have hn : (n : ℝ) = 2 * V1.card := by exact_mod_cast hV1.symm
    rw [hn] at h ⊢
    nlinarith [h]

lemma two_obj (G : SimpleGraph (Fin n)) (y : Fin n → Fin n → ℝ) (hs : ∀ i j, y i j = y j i) :
    2 * lpObj G y = ∑ i, ∑ j, if G.Adj i j then y i j else 0 := by
  have := two_sum_lt (fun i j => if G.Adj i j then y i j else 0)
    (fun i j => by
      by_cases h : G.Adj i j
      · rw [if_pos h, if_pos (G.adj_symm h), hs]
      · rw [if_neg h, if_neg (fun h' => h (G.adj_symm h'))])
    (fun i => by simp)
  rw [← this]
  unfold lpObj
  simp only [ite_and]

end cut

section gapsec

variable {n : ℕ} {V1 : Finset (Fin n)} {x : Fin n → Fin n → ℝ}

lemma Sc_nonneg (hx : LPFeasible n x) (h3 : ∀ i j : Fin n, ∃ k, k ≠ i ∧ k ≠ j) :
    0 ≤ ∑ i, ∑ j, if ¬ sameSide V1 i j then dev V1 x i j else 0 :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs <;> first | exact le_refl _ | exact dev_nonneg hx h3 i j

lemma same_eq_cross (hV1 : IsBisection n V1) (hx : LPFeasible n x) :
    (∑ i, ∑ j, if sameSide V1 i j then dev V1 x i j else 0) =
      ∑ i, ∑ j, if ¬ sameSide V1 i j then dev V1 x i j else 0 := by
  have hc := cut_feasible V1 hV1
  have e1 := two_sum_lt x hx.1 hx.2.1
  have e2 := two_sum_lt (cutVec V1) hc.1 hc.2.1
  rw [hx.2.2.2.2] at e1
  rw [hc.2.2.2.2] at e2
  have e3 : (∑ i, ∑ j, (x i j - cutVec V1 i j)) = 0 := by
    simp only [Finset.sum_sub_distrib]; linarith
  have e4 : (∑ i, ∑ j, (x i j - cutVec V1 i j)) =
      (∑ i, ∑ j, if sameSide V1 i j then dev V1 x i j else 0) -
        ∑ i, ∑ j, if ¬ sameSide V1 i j then dev V1 x i j else 0 := by
    simp only [diff_dev, Finset.sum_sub_distrib]
  linarith

lemma obj_diff (hV1 : IsBisection n V1) (hx : LPFeasible n x) (G : SimpleGraph (Fin n)) :
    2 * (lpObj G x - lpObj G (cutVec V1)) =
      (∑ i, ∑ j, if G.Adj i j ∧ sameSide V1 i j then dev V1 x i j else 0) -
        ∑ i, ∑ j, if G.Adj i j ∧ ¬ sameSide V1 i j then dev V1 x i j else 0 := by
  have hc := cut_feasible V1 hV1
  rw [mul_sub, two_obj G x hx.1, two_obj G (cutVec V1) hc.1]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hG : G.Adj i j
  · simp only [hG, true_and, if_true]; exact diff_dev i j
  · simp [hG]

lemma gap (hV1 : IsBisection n V1) (hx : LPFeasible n x) (h3 : ∀ i j : Fin n, ∃ k, k ≠ i ∧ k ≠ j)
    (G : SimpleGraph (Fin n)) (H1 : SimpleGraph (Fin n)) (din : ℕ)
    (hH1 : ∀ i j, H1.Adj i j → sameSide V1 i j ∧ G.Adj i j) (hH1d : ∀ v, inDeg H1 V1 v = din)
    (H0 : SimpleGraph (Fin n)) (dout : ℕ) (hH0s : ∀ i j, H0.Adj i j → ¬ sameSide V1 i j)
    (hH0G : ∀ i j, G.Adj i j → ¬ sameSide V1 i j → H0.Adj i j)
    (hH0d : ∀ v, outDeg H0 V1 v = dout) (hdd : (din : ℝ) - dout ≥ V1.card / 2) :
    2 * (∑ i, ∑ j, if ¬ sameSide V1 i j then dev V1 x i j else 0) ≤
      (V1.card : ℝ) * (2 * (lpObj G x - lpObj G (cutVec V1))) := by
  have hH1s : ∀ i j, H1.Adj i j → sameSide V1 i j := fun i j h => (hH1 i j h).1
  have hAP : (∑ i, ∑ j, if H1.Adj i j then dev V1 x i j else 0) ≤
      ∑ i, ∑ j, if G.Adj i j ∧ sameSide V1 i j then dev V1 x i j else 0 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      by_cases hh : H1.Adj i j
      · rw [if_pos hh, if_pos ⟨(hH1 i j hh).2, (hH1 i j hh).1⟩]
      · rw [if_neg hh]; split_ifs
        · exact dev_nonneg hx h3 i j
        · exact le_refl _
  have hBQ : (∑ i, ∑ j, if G.Adj i j ∧ ¬ sameSide V1 i j then dev V1 x i j else 0) ≤
      ∑ i, ∑ j, if H0.Adj i j then dev V1 x i j else 0 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      by_cases hh : G.Adj i j ∧ ¬ sameSide V1 i j
      · rw [if_pos hh, if_pos (hH0G i j hh.1 hh.2)]
      · rw [if_neg hh]; split_ifs
        · exact dev_nonneg hx h3 i j
        · exact le_refl _
  have hsplit := split_same hx H1 hH1s
  have hsum := same_eq_cross hV1 hx
  have hQ := Qbound hV1 hx H0 dout hH0s hH0d
  have hN := Nbound hV1 hx H1 din hH1s hH1d
  have hSc := Sc_nonneg (V1 := V1) hx h3
  rw [obj_diff hV1 hx G]
  set A := (∑ i, ∑ j, if G.Adj i j ∧ sameSide V1 i j then dev V1 x i j else 0)
  set B := (∑ i, ∑ j, if G.Adj i j ∧ ¬ sameSide V1 i j then dev V1 x i j else 0)
  set P := (∑ i, ∑ j, if H1.Adj i j then dev V1 x i j else 0)
  set Q := (∑ i, ∑ j, if H0.Adj i j then dev V1 x i j else 0)
  set N := (∑ i, ∑ j, if Pn V1 H1 i j then dev V1 x i j else 0)
  set Ss := (∑ i, ∑ j, if sameSide V1 i j then dev V1 x i j else 0)
  set Sc := (∑ i, ∑ j, if ¬ sameSide V1 i j then dev V1 x i j else 0)
  set m : ℝ := (V1.card : ℝ)
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have k1 : m * P ≤ m * A := mul_le_mul_of_nonneg_left hAP hm0
  have k2 : m * B ≤ m * Q := mul_le_mul_of_nonneg_left hBQ hm0
  have k3 : 0 ≤ Sc * (2 * din - 2 * dout - m) := mul_nonneg hSc (by linarith)
  have k4 : m * Ss = m * P + m * N := by rw [hsplit]; ring
  have k5 : m * Ss = m * Sc := by rw [hsum]
  have k6 : (dout : ℝ) * (Ss + Sc) = 2 * dout * Sc := by rw [hsum]; ring
  nlinarith [k1, k2, k3, k4, k5, k6, hQ, hN]

lemma eq_cut (hx : LPFeasible n x) (h3 : ∀ i j : Fin n, ∃ k, k ≠ i ∧ k ≠ j)
    (hsum : (∑ i, ∑ j, if sameSide V1 i j then dev V1 x i j else 0) =
      ∑ i, ∑ j, if ¬ sameSide V1 i j then dev V1 x i j else 0)
    (h0 : (∑ i, ∑ j, if ¬ sameSide V1 i j then dev V1 x i j else 0) = 0) :
    x = cutVec V1 := by
  have tot : (∑ i, ∑ j, dev V1 x i j) = 0 := by
    have : (∑ i, ∑ j, dev V1 x i j) =
        (∑ i, ∑ j, if sameSide V1 i j then dev V1 x i j else 0) +
          ∑ i, ∑ j, if ¬ sameSide V1 i j then dev V1 x i j else 0 := by
      simp only [← Finset.sum_add_distrib, total_dev]
    rw [this, hsum, h0]; ring
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg fun j _ => dev_nonneg (V1 := V1) hx h3 i j)).mp tot
  funext i j
  have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => dev_nonneg (V1 := V1) hx h3 i j)).mp
    (hrow i (Finset.mem_univ _)) j (Finset.mem_univ _)
  unfold dev at hij
  unfold cutVec
  by_cases h : sameSide V1 i j
  · rw [if_pos h] at hij ⊢; exact hij
  · rw [if_neg h] at hij ⊢; linarith

end gapsec

end LPR4

open LPCommunity.LPRecovery in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n))
    (hV1 : LPCommunity.MinBisect.IsBisection n V1) (din dout : ℕ)
    (h1 : ∃ H : SimpleGraph (Fin n), (∀ i j, H.Adj i j → LPCommunity.MinBisect.sameSide V1 i j ∧ G.Adj i j) ∧
      ∀ v, LPCommunity.MinBisect.inDeg H V1 v = din)
    (h0 : ∃ H : SimpleGraph (Fin n), (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
      (∀ i j, G.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j → H.Adj i j) ∧ ∀ v, LPCommunity.MinBisect.outDeg H V1 v = dout)
    (h : (din : ℝ) - dout ≥ (n : ℝ) / 4) :
    LPRecovers G V1 := by
  obtain ⟨H1, hH1, hH1d⟩ := h1
  obtain ⟨H0, hH0s, hH0G, hH0d⟩ := h0
  have hc := LPR4.cut_feasible V1 hV1
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    refine ⟨⟨hc, fun y _ => by simp [lpObj]⟩, fun y _ => ?_⟩
    funext i; exact i.elim0
  have hH1s : ∀ i j, H1.Adj i j → LPCommunity.MinBisect.sameSide V1 i j := fun i j h => (hH1 i j h).1
  have hbis := hV1
  unfold LPCommunity.MinBisect.IsBisection at hbis
  have hn : (n : ℝ) = 2 * V1.card := by exact_mod_cast hbis.symm
  have hdd : (din : ℝ) - dout ≥ V1.card / 2 := by rw [hn] at h; linarith
  have hP0 := LPR4.cardP hV1 H1 din hH1s hH1d ⟨0, hnpos⟩
  have hPnn : (0:ℝ) ≤ ((univ.filter fun j => LPR4.Pn V1 H1 ⟨0, hnpos⟩ j).card : ℝ) :=
    Nat.cast_nonneg _
  have hdout : (0:ℝ) ≤ dout := Nat.cast_nonneg _
  have hm2 : (2:ℝ) ≤ V1.card := by linarith
  have hn3 : 3 ≤ n := by
    have : (3:ℝ) ≤ n := by linarith
    exact_mod_cast this
  have h3 : ∀ i j : Fin n, ∃ k, k ≠ i ∧ k ≠ j := by
    intro i j
    by_contra hcon
    push Not at hcon
    have hsub : (univ : Finset (Fin n)) ⊆ {i, j} := by
      intro k _
      by_cases hk : k = i
      · simp [hk]
      · simp [hcon k hk]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    have := Finset.card_le_two (a := i) (b := j)
    omega
  have hm : (0:ℝ) < V1.card := by linarith
  refine ⟨⟨hc, fun y hy => ?_⟩, fun y hy => ?_⟩
  · have g := LPR4.gap hV1 hy h3 G H1 din hH1 hH1d H0 dout hH0s hH0G hH0d hdd
    have hS := LPR4.Sc_nonneg (V1 := V1) hy h3
    nlinarith
  · have g := LPR4.gap hV1 hy.1 h3 G H1 din hH1 hH1d H0 dout hH0s hH0G hH0d hdd
    have hS := LPR4.Sc_nonneg (V1 := V1) hy.1 h3
    have hle := hy.2 _ hc
    have hz : (∑ i, ∑ j, if ¬ LPCommunity.MinBisect.sameSide V1 i j then LPR4.dev V1 y i j else 0)
        = 0 := by nlinarith
    exact LPR4.eq_cut hy.1 h3 (LPR4.same_eq_cross hV1 hy.1) hz
