-- Prove2me | solution 1 for MulticlassQNet.SingleStation.theorem_8_4_projection_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T15:04:47.709498+00:00
-- url     : https://prove2.me/submissions/7efd144c-fe37-4a56-acfa-a0e7ff2af23b

import Mathlib
import Definitions.Def_MulticlassQNet_SingleStation_Polyhedra



namespace MulticlassQNet.SingleStation

open Finset

noncomputable def eP {n : ℕ} (P : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ p ∈ P, if p.1 ∈ S ∧ p.2 ∈ S then w p else 0

theorem eP_super {n : ℕ} (P : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (S T : Finset (Fin n)) :
    eP P w S + eP P w T ≤ eP P w (S ∪ T) + eP P w (S ∩ T) := by
  unfold eP
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have := hw p hp
  simp only [mem_union, mem_inter]
  by_cases h1 : p.1 ∈ S <;> by_cases h2 : p.2 ∈ S <;> by_cases h3 : p.1 ∈ T <;>
    by_cases h4 : p.2 ∈ T <;> simp [h1, h2, h3, h4] <;> linarith

theorem split_core {n : ℕ} (w : Fin n × Fin n → ℝ) (P : Finset (Fin n × Fin n)) :
    ∀ d : Fin n → ℝ, (∀ p ∈ P, p.1 ≠ p.2) → (∀ p ∈ P, 0 ≤ w p) →
      (∀ S, eP P w S ≤ ∑ j ∈ S, d j) → ∑ j, d j = eP P w univ →
      ∃ t : Fin n × Fin n → ℝ, (∀ p ∈ P, 0 ≤ t p ∧ t p ≤ w p) ∧
        ∀ j, d j = ∑ p ∈ P, ((if p.1 = j then t p else 0) +
          (if p.2 = j then w p - t p else 0)) := by
  induction P using Finset.induction_on with
  | empty =>
    intro d _ _ hS htot
    refine ⟨0, by simp, ?_⟩
    simp only [eP, sum_empty] at hS htot ⊢
    have hnn : ∀ j, 0 ≤ d j := fun j => by simpa using hS {j}
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 htot j (mem_univ j)
  | insert q P hq ih =>
    intro d hne hw hS htot
    have hq12 : q.1 ≠ q.2 := hne q (mem_insert_self _ _)
    have hwq : 0 ≤ w q := hw q (mem_insert_self _ _)
    let F : Finset (Fin n) → ℝ := fun S => ∑ j ∈ S, d j - eP (insert q P) w S
    have hF : ∀ S, 0 ≤ F S := fun S => sub_nonneg.2 (hS S)
    obtain ⟨S0, hS0mem, hS0min⟩ := Finset.exists_min_image
      (univ.filter (fun S : Finset (Fin n) => q.1 ∈ S ∧ q.2 ∉ S)) F
      ⟨{q.1}, by simpa using Ne.symm hq12⟩
    obtain ⟨T0, hT0mem, hT0min⟩ := Finset.exists_min_image
      (univ.filter (fun S : Finset (Fin n) => q.2 ∈ S ∧ q.1 ∉ S)) F
      ⟨{q.2}, by simpa using hq12⟩
    simp only [mem_filter, mem_univ, true_and] at hS0mem hT0mem hS0min hT0min
    have heP : ∀ S, eP (insert q P) w S = eP P w S + (if q.1 ∈ S ∧ q.2 ∈ S then w q else 0) := by
      intro S; unfold eP; rw [sum_insert hq]; ring
    have key : w q ≤ F S0 + F T0 := by
      have hsup := eP_super P w (fun p hp => hw p (mem_insert_of_mem hp)) S0 T0
      have hU := hS (S0 ∪ T0)
      have hV := hS (S0 ∩ T0)
      have hd := sum_union_inter (s₁ := S0) (s₂ := T0) (f := d)
      have e1 := heP S0
      have e2 := heP T0
      have e3 := heP (S0 ∪ T0)
      have e4 := heP (S0 ∩ T0)
      simp only [mem_union, mem_inter, hS0mem.1, hS0mem.2, hT0mem.1, hT0mem.2, true_or, or_true,
        and_true, and_false, false_and, true_and, if_true, if_false] at e1 e2 e3 e4
      simp only [F]
      linarith
    set t0 := min (F S0) (w q) with ht0
    have ht0a : t0 ≤ F S0 := min_le_left _ _
    have ht0b : t0 ≤ w q := min_le_right _ _
    have ht0c : 0 ≤ t0 := le_min (hF S0) hwq
    have ht0d : w q - t0 ≤ F T0 := by
      rcases min_cases (F S0) (w q) with h | h
      · rw [ht0, h.1]; linarith
      · rw [ht0, h.1]; linarith [hF T0]
    let d' : Fin n → ℝ := fun j =>
      d j - (if q.1 = j then t0 else 0) - (if q.2 = j then w q - t0 else 0)
    have hd'S : ∀ S, ∑ j ∈ S, d' j =
        ∑ j ∈ S, d j - (if q.1 ∈ S then t0 else 0) - (if q.2 ∈ S then w q - t0 else 0) := by
      intro S; simp only [d', sum_sub_distrib, sum_ite_eq]
    have hA : ∀ S, eP P w S ≤ ∑ j ∈ S, d' j := by
      intro S
      have h1 := hS S
      have h2 := heP S
      rw [hd'S S]
      by_cases ha : q.1 ∈ S <;> by_cases hb : q.2 ∈ S
      · simp only [ha, hb, and_self, if_true] at h2 ⊢; linarith
      · have := hS0min S ⟨ha, hb⟩
        simp only [ha, hb, and_false, if_false, if_true] at h2 ⊢
        simp only [F] at this ht0a; linarith
      · have := hT0min S ⟨hb, ha⟩
        simp only [ha, hb, false_and, if_false, if_true] at h2 ⊢
        simp only [F] at this ht0d; linarith
      · simp only [ha, hb, false_and, if_false] at h2 ⊢; linarith
    have hB : ∑ j, d' j = eP P w univ := by
      have h2 := heP univ
      have h3 := hd'S univ
      simp only [mem_univ, and_self, if_true] at h2 h3
      linarith
    obtain ⟨t, ht, hd⟩ := ih d' (fun p hp => hne p (mem_insert_of_mem hp))
      (fun p hp => hw p (mem_insert_of_mem hp)) hA hB
    refine ⟨Function.update t q t0, ?_, ?_⟩
    · intro p hp
      rcases mem_insert.1 hp with rfl | hp'
      · simp [ht0c, ht0b]
      · have hpq : p ≠ q := fun h => hq (h ▸ hp')
        simpa [Function.update_of_ne hpq] using ht p hp'
    · intro j
      rw [sum_insert hq]
      have hrest : ∑ p ∈ P, ((if p.1 = j then Function.update t q t0 p else 0) +
          (if p.2 = j then w p - Function.update t q t0 p else 0)) =
          ∑ p ∈ P, ((if p.1 = j then t p else 0) + (if p.2 = j then w p - t p else 0)) := by
        apply sum_congr rfl
        intro p hp
        have hpq : p ≠ q := fun h => hq (h ▸ hp)
        rw [Function.update_of_ne hpq]
      rw [hrest, ← hd j]
      simp only [d', Function.update_self]
      ring

theorem p2_key {n : ℕ} (lam mu : Fin n → ℝ) (hmu : ∀ i, 0 < mu i)
    (x : Fin n → ℝ) (I : Fin n → Fin n → ℝ) (h : (x, I) ∈ P2 lam mu) (S : Finset (Fin n)) :
    ∑ j ∈ S, (∑ i ∈ S, I i j) / mu j =
      (∑ i ∈ S, rho lam mu i) * (∑ i ∈ S, 1 / mu i * x i) + ∑ i ∈ S, rho lam mu i / mu i := by
  obtain ⟨_, _, hd, hoff, _⟩ := h
  simp only at hd hoff
  have hpair : ∀ i j, I i j / mu j + I j i / mu i =
      rho lam mu j * (1 / mu i * x i) + rho lam mu i * (1 / mu j * x j) +
        (if i = j then 2 * (rho lam mu i / mu i) else 0) := by
    intro i j
    have hi := hmu i; have hj := hmu j
    unfold rho
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have := hd i
      field_simp
      nlinarith [this]
    · simp only [hij, if_false]
      have := hoff i j hij
      field_simp
      nlinarith [this]
  have h2 : 2 * ∑ j ∈ S, (∑ i ∈ S, I i j) / mu j =
      ∑ i ∈ S, ∑ j ∈ S, (I i j / mu j + I j i / mu i) := by
    simp only [Finset.sum_add_distrib, Finset.sum_div]
    rw [Finset.sum_comm (f := fun i j => I j i / mu i)]
    rw [Finset.sum_comm (f := fun i j => I i j / mu j)]
    ring
  have h3 : ∑ i ∈ S, ∑ j ∈ S, (I i j / mu j + I j i / mu i) =
      2 * ((∑ i ∈ S, rho lam mu i) * (∑ i ∈ S, 1 / mu i * x i) + ∑ i ∈ S, rho lam mu i / mu i) := by
    simp only [hpair, Finset.sum_add_distrib]
    have e1 : ∑ i ∈ S, ∑ j ∈ S, rho lam mu j * (1 / mu i * x i) =
        (∑ i ∈ S, rho lam mu i) * (∑ i ∈ S, 1 / mu i * x i) := by
      rw [Finset.sum_mul_sum, Finset.sum_comm]
    have e2 : ∑ i ∈ S, ∑ j ∈ S, rho lam mu i * (1 / mu j * x j) =
        (∑ i ∈ S, rho lam mu i) * (∑ i ∈ S, 1 / mu i * x i) := by
      rw [Finset.sum_mul_sum]
    have e3 : ∑ i ∈ S, ∑ j ∈ S, (if i = j then 2 * (rho lam mu i / mu i) else 0) =
        2 * ∑ i ∈ S, rho lam mu i / mu i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
      rw [Finset.sum_ite_eq]; simp [hi]
    rw [e1, e2, e3]; ring
  linarith

theorem proj_subset_core {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    {x : Fin n → ℝ | ∃ I, (x, I) ∈ P2 lam mu} ⊆ P1 lam mu := by
  rintro x ⟨I, hI⟩
  have hI' := hI
  obtain ⟨hx, hInn, _, _, hcol⟩ := hI'
  simp only at hx hInn hcol
  have hrho : ∀ S : Finset (Fin n), ∑ i ∈ S, rho lam mu i < 1 := by
    intro S
    refine lt_of_le_of_lt ?_ hload
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => (div_pos (hlam i) (hmu i)).le)
  have hbound : ∀ S : Finset (Fin n), ∑ j ∈ S, (∑ i ∈ S, I i j) / mu j ≤ ∑ i ∈ S, 1 / mu i * x i := by
    intro S
    apply Finset.sum_le_sum
    intro j _
    rw [div_eq_inv_mul, one_div, ← hcol j]
    apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (hmu j)).le
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => hInn i j)
  have hfull : ∑ j ∈ (univ : Finset (Fin n)), (∑ i ∈ univ, I i j) / mu j =
      ∑ i ∈ (univ : Finset (Fin n)), 1 / mu i * x i := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hcol j]; ring
  refine ⟨hx, ?_, ?_⟩
  · intro S _
    show b lam mu S ≤ _
    unfold b
    have h1 := hrho S
    rw [div_le_iff₀ (by linarith)]
    have := p2_key lam mu hmu x I hI S
    have := hbound S
    nlinarith
  · show _ = b lam mu univ
    unfold b
    have h1 := hrho univ
    rw [eq_div_iff (by linarith)]
    have := p2_key lam mu hmu x I hI univ
    rw [hfull] at this
    linarith


theorem eP_pairs {n : ℕ} (r y : Fin n → ℝ) (S : Finset (Fin n)) :
    eP (univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (fun p => r p.2 * y p.1 + r p.1 * y p.2) S =
      (∑ i ∈ S, r i) * (∑ i ∈ S, y i) - ∑ i ∈ S, r i * y i := by
  unfold eP
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only
  set g : Fin n → Fin n → ℝ := fun i j =>
    if i < j then (if i ∈ S ∧ j ∈ S then r j * y i + r i * y j else 0) else 0 with hg
  set C : Fin n → Fin n → ℝ := fun i j =>
    if i ∈ S ∧ j ∈ S ∧ i ≠ j then r j * y i else 0 with hC
  have hpt : ∀ i j, g i j + g j i = C i j + C j i := by
    intro i j
    simp only [hg, hC]
    rcases lt_trichotomy i j with h | h | h
    · have h1 : ¬ j < i := lt_asymm h
      have h2 : i ≠ j := ne_of_lt h
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [h, h1, h2, Ne.symm h2, hi, hj] <;> ring
    · subst h; simp
    · have h1 : ¬ i < j := lt_asymm h
      have h2 : j ≠ i := ne_of_lt h
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [h, h1, h2, Ne.symm h2, hi, hj] <;> ring
  have h2 : 2 * ∑ i, ∑ j, g i j = 2 * ∑ i, ∑ j, C i j := by
    have e1 : ∑ i, ∑ j, (g i j + g j i) = 2 * ∑ i, ∑ j, g i j := by
      simp only [Finset.sum_add_distrib]; rw [Finset.sum_comm (f := fun i j => g j i)]; ring
    have e2 : ∑ i, ∑ j, (C i j + C j i) = 2 * ∑ i, ∑ j, C i j := by
      simp only [Finset.sum_add_distrib]; rw [Finset.sum_comm (f := fun i j => C j i)]; ring
    rw [← e1, ← e2]; simp only [hpt]
  have hCsum : ∑ i, ∑ j, C i j = (∑ i ∈ S, r i) * (∑ i ∈ S, y i) - ∑ i ∈ S, r i * y i := by
    have hpt2 : ∀ i j, C i j = (if i ∈ S then (if j ∈ S then r j * y i else 0) else 0) -
        (if i = j then (if i ∈ S then r i * y i else 0) else 0) := by
      intro i j
      simp only [hC]
      by_cases hij : i = j
      · subst hij; by_cases hi : i ∈ S <;> simp [hi]
      · by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj, hij]
    have hD : ∑ i, ∑ j, (if i ∈ S then (if j ∈ S then r j * y i else 0) else 0) =
        (∑ i ∈ S, r i) * (∑ i ∈ S, y i) := by
      calc ∑ i, ∑ j, (if i ∈ S then (if j ∈ S then r j * y i else 0) else 0)
          = ∑ i, (if i ∈ S then ∑ j ∈ S, r j * y i else 0) := by
            apply Finset.sum_congr rfl; intro i _
            by_cases hi : i ∈ S
            · simp only [hi, if_true]; rw [Finset.sum_ite_mem, Finset.univ_inter]
            · simp [hi]
        _ = ∑ i ∈ S, ∑ j ∈ S, r j * y i := by rw [Finset.sum_ite_mem, Finset.univ_inter]
        _ = (∑ i ∈ S, r i) * (∑ i ∈ S, y i) := by
            rw [Finset.sum_mul_sum, Finset.sum_comm]
    have hE : ∑ i, ∑ j, (if i = j then (if i ∈ S then r i * y i else 0) else 0) =
        ∑ i ∈ S, r i * y i := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp only [hpt2, Finset.sum_sub_distrib]
    rw [hD, hE]
  have : ∑ i, ∑ j, g i j = ∑ i, ∑ j, C i j := by linarith
  rw [this, hCsum]

theorem col_conv {n : ℕ} (t w : Fin n × Fin n → ℝ) (j : Fin n) :
    ∑ p ∈ univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      ((if p.1 = j then t p else 0) + (if p.2 = j then w p - t p else 0)) =
    ∑ i, ((if j < i then t (j, i) else 0) + (if i < j then w (i, j) - t (i, j) else 0)) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only
  have h1 : ∀ a b : Fin n, (if a < b then ((if a = j then t (a, b) else 0) +
      (if b = j then w (a, b) - t (a, b) else 0)) else 0) =
      (if a = j then (if j < b then t (j, b) else 0) else 0) +
      (if b = j then (if a < j then w (a, j) - t (a, j) else 0) else 0) := by
    intro a b
    by_cases ha : a = j <;> by_cases hb : b = j
    · subst ha; subst hb; simp
    · subst ha; by_cases hab : a < b <;> simp [hab, hb]
    · subst hb; by_cases hab : a < b <;> simp [hab, ha]
    · by_cases hab : a < b <;> simp [hab, ha, hb]
  simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun x y => if x = j then (if j < y then t (j, y) else 0) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem proj_supset_core {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    P1 lam mu ⊆ {x : Fin n → ℝ | ∃ I, (x, I) ∈ P2 lam mu} := by
  intro x hx
  unfold P1 AllocationIndices.achievablePolytope at hx
  obtain ⟨hx0, hxS, hxU⟩ := hx
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun i => 1 / mu i * x i := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Fin n → ℝ, r = rho lam mu := ⟨_, rfl⟩
  have hr0 : ∀ i, 0 ≤ r i := fun i => by rw [hr]; exact (div_pos (hlam i) (hmu i)).le
  have hy0 : ∀ i, 0 ≤ y i := fun i => by
    rw [hy]; exact mul_nonneg (one_div_pos.2 (hmu i)).le (hx0 i)
  have hrho : ∀ S : Finset (Fin n), ∑ i ∈ S, r i < 1 := by
    intro S
    refine lt_of_le_of_lt ?_ hload
    rw [hr]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => (div_pos (hlam i) (hmu i)).le)
  have hb : ∀ S, b lam mu S = (∑ i ∈ S, r i / mu i) / (1 - ∑ i ∈ S, r i) := by
    intro S; rw [hr]; rfl
  have hY : ∀ S : Finset (Fin n), ∑ i ∈ S, 1 / mu i * x i = ∑ i ∈ S, y i := by
    intro S; rw [hy]
  let P : Finset (Fin n × Fin n) := univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let w : Fin n × Fin n → ℝ := fun p => r p.2 * y p.1 + r p.1 * y p.2
  let d : Fin n → ℝ := fun j => y j - r j * y j - r j / mu j
  have hdS : ∀ S : Finset (Fin n), ∑ j ∈ S, d j =
      ∑ j ∈ S, y j - ∑ j ∈ S, r j * y j - ∑ j ∈ S, r j / mu j := by
    intro S; simp only [d, Finset.sum_sub_distrib]
  have hne : ∀ p ∈ P, p.1 ≠ p.2 := by
    intro p hp; simp only [P, mem_filter, mem_univ, true_and] at hp; exact ne_of_lt hp
  have hw : ∀ p ∈ P, 0 ≤ w p := fun p _ => by
    simp only [w]; nlinarith [hr0 p.1, hr0 p.2, hy0 p.1, hy0 p.2]
  have hS : ∀ S, eP P w S ≤ ∑ j ∈ S, d j := by
    intro S
    rw [eP_pairs r y S, hdS S]
    by_cases hSu : S = univ
    · subst hSu
      have h := hxU
      rw [hb, hY, eq_div_iff (by linarith [hrho univ])] at h
      nlinarith
    · have h := hxS S hSu
      rw [hb, hY, div_le_iff₀ (by linarith [hrho S])] at h
      nlinarith
  have htot : ∑ j, d j = eP P w univ := by
    rw [eP_pairs r y univ, hdS univ]
    have h := hxU
    rw [hb, hY, eq_div_iff (by linarith [hrho univ])] at h
    nlinarith
  obtain ⟨t, ht, hd⟩ := split_core w P d hne hw hS htot
  have htP : ∀ i j, i < j → 0 ≤ t (i, j) ∧ t (i, j) ≤ w (i, j) := by
    intro i j hij; exact ht (i, j) (by simp [P, hij])
  refine ⟨fun i j => if i = j then lam i * (x i + 1) / mu i else
    mu j * ((if i < j then w (i, j) - t (i, j) else 0) + (if j < i then t (j, i) else 0)), ?_⟩
  refine ⟨hx0, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only
    split_ifs with h1 h2 h3 h3
    · have := hlam i; have := hmu i; have := hx0 i; positivity
    · exact absurd (lt_trans h2 h3) (lt_irrefl _)
    · have := htP i j h2; have := hmu j; nlinarith
    · have := htP j i h3; have := hmu j; nlinarith
    · have := hmu j; simp
  · intro i
    simp only [if_true]
    have := hmu i; field_simp; ring
  · intro i j hij
    simp only [hij, Ne.symm hij, if_false]
    have hmi := hmu i; have hmj := hmu j
    have hyi : y i = x i / mu i := by rw [hy]; simp; ring
    have hyj : y j = x j / mu j := by rw [hy]; simp; ring
    have hri : r i = lam i / mu i := by rw [hr]; rfl
    have hrj : r j = lam j / mu j := by rw [hr]; rfl
    rcases lt_or_gt_of_ne hij with h | h
    · have h' : ¬ j < i := lt_asymm h
      simp only [h, h', if_true, if_false, w, hyi, hyj, hri, hrj]
      field_simp; ring
    · have h' : ¬ i < j := lt_asymm h
      simp only [h, h', if_true, if_false, w, hyi, hyj, hri, hrj]
      field_simp; ring
  · intro j
    have hdj := hd j
    rw [col_conv] at hdj
    have hsplit : ∀ i, (if i = j then lam i * (x i + 1) / mu i else
        mu j * ((if i < j then w (i, j) - t (i, j) else 0) + (if j < i then t (j, i) else 0))) =
        (if i = j then lam j * (x j + 1) / mu j else 0) +
        mu j * ((if j < i then t (j, i) else 0) + (if i < j then w (i, j) - t (i, j) else 0)) := by
      intro i
      by_cases hij : i = j
      · subst hij; simp
      · simp only [hij, if_false]; ring
    simp only
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← hdj, Finset.sum_ite_eq', if_pos (mem_univ _)]
    have hmj := hmu j
    have hyj : y j = x j / mu j := by rw [hy]; simp; ring
    have hrj : r j = lam j / mu j := by rw [hr]; rfl
    simp only [d, hyj, hrj]
    field_simp; ring

theorem projection_eq_core {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    {x : Fin n → ℝ | ∃ I, (x, I) ∈ P2 lam mu} = P1 lam mu :=
  Set.Subset.antisymm (proj_subset_core lam mu hlam hmu hload)
    (proj_supset_core lam mu hlam hmu hload)

end MulticlassQNet.SingleStation

open MulticlassQNet.SingleStation


theorem solution {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    {x : Fin n → ℝ | ∃ I, (x, I) ∈ P2 lam mu} = P1 lam mu := by
  exact projection_eq_core lam mu hlam hmu hload
