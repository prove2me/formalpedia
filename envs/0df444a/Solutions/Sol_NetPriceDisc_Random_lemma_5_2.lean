-- Prove2me | solution 1 for NetPriceDisc.Random.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:08:13.417981+00:00
-- url     : https://prove2.me/submissions/9bb82c8f-3889-4585-9e0a-2c7b7b6884f2

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model

set_option autoImplicit false
open Matrix NetPriceDisc.Random

lemma E_sub {α : Type*} [DecidableEq α] (D T : Finset α) (hT : T ⊆ D) (q : ℝ) :
    ∑ S ∈ D.powerset, q ^ S.card * (1 - q) ^ (D.card - S.card) * (if T ⊆ S then (1 : ℝ) else 0)
      = q ^ T.card := by
  have h := Finset.prod_add (fun _ : α => q) (fun d => if d ∈ T then (0 : ℝ) else 1 - q) D
  have h1 : ∏ d ∈ D, (q + (if d ∈ T then (0 : ℝ) else 1 - q)) = q ^ T.card := by
    have : ∀ d ∈ D, (q + (if d ∈ T then (0 : ℝ) else 1 - q)) = if d ∈ T then q else 1 := by
      intro d _
      split_ifs <;> ring
    rw [Finset.prod_congr rfl this, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
      mul_one]
    congr 2
    ext x; simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hT h, h⟩⟩
  rw [h1] at h
  rw [h]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have hSD : S ⊆ D := Finset.mem_powerset.mp hS
  rw [Finset.prod_const]
  by_cases hTS : T ⊆ S
  · rw [if_pos hTS]
    have : ∏ d ∈ D \ S, (if d ∈ T then (0 : ℝ) else 1 - q) = (1 - q) ^ (D.card - S.card) := by
      rw [Finset.prod_congr rfl (g := fun _ => 1 - q), Finset.prod_const, Finset.card_sdiff_of_subset hSD]
      intro d hd
      have : d ∉ T := fun h => (Finset.mem_sdiff.mp hd).2 (hTS h)
      simp [this]
    rw [this]; ring
  · rw [if_neg hTS]
    obtain ⟨d, hdT, hdS⟩ := Finset.not_subset.mp hTS
    have : ∏ d ∈ D \ S, (if d ∈ T then (0 : ℝ) else 1 - q) = 0 :=
      Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hT hdT, hdS⟩) (by simp [hdT])
    rw [this]; ring

lemma P_val (n : ℕ) (q : ℝ) (e f : Fin n × Fin n) :
    erExpect n q (fun G => G e.1 e.2 * G f.1 f.2) =
      if e.1 ≠ e.2 ∧ f.1 ≠ f.2 then (if e = f then q else q ^ 2) else 0 := by
  unfold erExpect
  set D := (Finset.univ : Finset (Fin n)).offDiag with hD
  have hind : ∀ S : Finset (Fin n × Fin n), (adjOf S e.1 e.2) * (adjOf S f.1 f.2) =
      if ({e, f} : Finset (Fin n × Fin n)) ⊆ S then 1 else 0 := by
    intro S
    simp only [adjOf, Prod.mk.eta]
    by_cases h1 : e ∈ S <;> by_cases h2 : f ∈ S <;> simp [h1, h2, Finset.insert_subset_iff]
  by_cases hef : e.1 ≠ e.2 ∧ f.1 ≠ f.2
  · rw [if_pos hef]
    have hT : ({e, f} : Finset (Fin n × Fin n)) ⊆ D := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [hD, Finset.mem_offDiag, hef.1]
      · simp [hD, Finset.mem_offDiag, hef.2]
    have := E_sub D {e, f} hT q
    simp only [hind]
    rw [show (∑ S ∈ D.powerset, q ^ S.card * (1 - q) ^ (D.card - S.card) *
        (if ({e, f} : Finset (Fin n × Fin n)) ⊆ S then (1 : ℝ) else 0)) = q ^ ({e, f} : Finset (Fin n × Fin n)).card from this]
    by_cases hef' : e = f
    · subst hef'; simp
    · rw [if_neg hef', Finset.card_pair hef']
  · rw [if_neg hef]
    apply Finset.sum_eq_zero
    intro S hS
    have hSD : S ⊆ D := Finset.mem_powerset.mp hS
    have : adjOf S e.1 e.2 * adjOf S f.1 f.2 = 0 := by
      simp only [adjOf, Prod.mk.eta]
      by_cases h1 : e ∈ S
      · by_cases h2 : f ∈ S
        · exfalso
          apply hef
          have h1' := hSD h1; have h2' := hSD h2
          simp only [hD, Finset.mem_offDiag] at h1' h2'
          exact ⟨h1'.2.2, h2'.2.2⟩
        · simp [h2]
      · simp [h1]
    show _ * (adjOf S e.1 e.2 * adjOf S f.1 f.2) = 0
    rw [this]; ring

lemma erExpect_add (n : ℕ) (q : ℝ) (F F' : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    erExpect n q (fun G => F G + F' G) = erExpect n q F + erExpect n q F' := by
  unfold erExpect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

lemma erExpect_sum {ι : Type*} (n : ℕ) (q : ℝ) (s : Finset ι)
    (F : ι → Matrix (Fin n) (Fin n) ℝ → ℝ) :
    erExpect n q (fun G => ∑ x ∈ s, F x G) = ∑ x ∈ s, erExpect n q (F x) := by
  unfold erExpect
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.mul_sum]

lemma walks2_expand {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) :
    walks (G + Gᵀ) 2 = ∑ i, ∑ j, ∑ l, (G i j + G j i) * (G j l + G l j) := by
  unfold walks
  simp only [pow_two, ones, dotProduct, Matrix.mulVec, Matrix.mul_apply, mul_one, one_mul,
    Matrix.add_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

lemma term_val (n : ℕ) (q : ℝ) (i j l : Fin n) :
    erExpect n q (fun G => (G i j + G j i) * (G j l + G l j)) =
      if i = j then 0 else if l = j then 0 else 4 * q ^ 2 + 2 * (q - q ^ 2) * (if l = i then 1 else 0) := by
  have h : (fun G : Matrix (Fin n) (Fin n) ℝ => (G i j + G j i) * (G j l + G l j)) =
      fun G => ((G i j * G j l + G i j * G l j) + G j i * G j l) + G j i * G l j := by
    funext G; ring
  rw [h, erExpect_add, erExpect_add, erExpect_add]
  have p1 := P_val n q (i, j) (j, l)
  have p2 := P_val n q (i, j) (l, j)
  have p3 := P_val n q (j, i) (j, l)
  have p4 := P_val n q (j, i) (l, j)
  simp only [] at p1 p2 p3 p4
  rw [p1, p2, p3, p4]
  by_cases hij : i = j
  · subst hij; simp
  · by_cases hlj : l = j
    · subst hlj; simp [hij]
    · by_cases hli : l = i
      · subst hli
        simp [hij, hlj, Ne.symm hij, Prod.ext_iff]
        ring
      · simp [hij, hlj, Ne.symm hij, Ne.symm hlj, hli, Ne.symm hli, Prod.ext_iff]
        ring

lemma sum_l (n : ℕ) (q : ℝ) (i j : Fin n) :
    ∑ l : Fin n, (if i = j then (0 : ℝ) else if l = j then 0 else
      4 * q ^ 2 + 2 * (q - q ^ 2) * (if l = i then 1 else 0)) =
    if i = j then 0 else 2 * q + (4 * n - 6) * q ^ 2 := by
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, if_false]
    have h : ∀ l : Fin n, (if l = j then (0 : ℝ) else
        4 * q ^ 2 + 2 * (q - q ^ 2) * (if l = i then 1 else 0)) =
        4 * q ^ 2 + 2 * (q - q ^ 2) * (if l = i then 1 else 0) - 4 * q ^ 2 * (if l = j then 1 else 0) := by
      intro l
      by_cases hl : l = j
      · have : l ≠ i := fun h => hij (h.symm.trans hl)
        have h' : ¬ j = i := fun h => this (hl.trans h)
        simp [hl, h']
      · simp [hl]
    simp only [h]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp
    ring

lemma sum_j (n : ℕ) (K : ℝ) (i : Fin n) :
    ∑ j : Fin n, (if i = j then (0 : ℝ) else K) = ((n : ℝ) - 1) * K := by
  have h : ∀ j : Fin n, (if i = j then (0 : ℝ) else K) = K - K * (if i = j then 1 else 0) := by
    intro j; split_ifs <;> simp
  simp only [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
  ring

theorem solution (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    erExpect n q (fun G => walks (G + Gᵀ) 2) =
      2 * (n : ℝ) * ((n : ℝ) - 1) * q * (1 - 3 * q + 2 * (n : ℝ) * q) := by
  have h : (fun G : Matrix (Fin n) (Fin n) ℝ => walks (G + Gᵀ) 2) =
      fun G => ∑ i, ∑ j, ∑ l, (G i j + G j i) * (G j l + G l j) := by
    funext G; exact walks2_expand G
  rw [h, erExpect_sum]
  simp only [erExpect_sum, term_val]
  have h2 : ∀ i : Fin n, (∑ x_1 : Fin n, ∑ x_2 : Fin n, (if i = x_1 then (0 : ℝ) else
      if x_2 = x_1 then 0 else 4 * q ^ 2 + 2 * (q - q ^ 2) * (if x_2 = i then 1 else 0))) =
      ((n : ℝ) - 1) * (2 * q + (4 * n - 6) * q ^ 2) := by
    intro i
    simp only [sum_l]
    exact sum_j n _ i
  simp only [h2]
  simp
  ring
