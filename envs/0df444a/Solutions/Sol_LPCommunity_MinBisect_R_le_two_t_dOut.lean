-- Prove2me | solution 1 for LPCommunity.MinBisect.R_le_two_t_dOut
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:59:58.696793+00:00
-- url     : https://prove2.me/submissions/49f6246f-df9e-4ee0-95fb-07a127a74222

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting

set_option autoImplicit false
open Finset
open scoped Classical
open LPCommunity.MinBisect

theorem W_eb_eq {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    edgesBetween G A B = ∑ a ∈ A, (B.filter (fun b => G.Adj a b)).card := by
  have h : edgesBetween G A B = ((A ×ˢ B).filter (fun q : Fin n × Fin n => G.Adj q.1 q.2)).card := by
    unfold edgesBetween
    apply Finset.card_nbij' (fun p => if p.1 ∈ A then p else p.swap)
      (fun q => if q.1 < q.2 then q else q.swap)
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hlt, hadj, hor⟩ := hp
      by_cases h1 : p.1 ∈ A
      · have h2 : p.2 ∈ B := by
          rcases hor with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h (Finset.disjoint_left.mp hAB h1)
        simp [h1, h2, hadj]
      · have h3 : p.1 ∈ B ∧ p.2 ∈ A := by
          rcases hor with ⟨h, _⟩ | h
          · exact absurd h h1
          · exact h
        simp [h1, h3.1, h3.2, hadj.symm]
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hqA, hqB⟩, hadj⟩ := hq
      have hne : q.1 ≠ q.2 := fun h => Finset.disjoint_left.mp hAB hqA (h ▸ hqB)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [hlt, hadj, hqA, hqB]
      · have : ¬ q.1 < q.2 := not_lt.mpr hgt.le
        simp [this, hgt, hadj.symm, hqA, hqB]
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hlt, hadj, hor⟩ := hp
      by_cases h1 : p.1 ∈ A
      · simp [h1, hlt]
      · have : ¬ (p.2 < p.1) := not_lt.mpr hlt.le
        simp [h1, this, hlt]
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hqA, hqB⟩, hadj⟩ := hq
      by_cases hlt : q.1 < q.2
      · simp [hlt, hqA]
      · have : q.2 ∉ A := fun h => Finset.disjoint_left.mp hAB h hqB
        simp [hlt, this]
  rw [h, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.card_filter]

theorem W_eb_comm {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    edgesBetween G A B = edgesBetween G B A := by
  unfold edgesBetween
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, h2, h3.symm⟩

theorem W_outdeg {n : ℕ} (G : SimpleGraph (Fin n)) (V1 A B : Finset (Fin n))
    (hA : ∀ a ∈ A, ∀ b ∈ B, ¬ sameSide V1 a b) :
    ∀ a ∈ A, (B.filter (fun b => G.Adj a b)).card ≤ dOut G V1 := by
  intro a ha
  calc (B.filter (fun b => G.Adj a b)).card ≤ outDeg G V1 a := by
        unfold outDeg
        apply Finset.card_le_card
        intro b hb
        rw [Finset.mem_filter] at hb ⊢
        exact ⟨Finset.mem_univ _, hb.2, hA a ha b hb.1⟩
    _ ≤ dOut G V1 := by
        unfold dOut
        exact Finset.le_sup (f := outDeg G V1) (Finset.mem_univ a)

theorem W_U2card {n : ℕ} (V1 W : Finset (Fin n)) (hV1 : IsBisection n V1)
    (hW : IsBisection n W) : (U2 V1 W).card = (V1 ∩ W).card := by
  unfold U2
  unfold IsBisection at hV1 hW
  have e1 : (V1ᶜ \ W).card + (V1ᶜ ∩ W).card = V1ᶜ.card := Finset.card_sdiff_add_card_inter _ _
  have e2 : (V1 ∩ W).card + (V1ᶜ ∩ W).card = W.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]; tauto
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_inter, Finset.mem_compl] at hx hx'
      tauto
  have e3 : V1ᶜ.card = n - V1.card := by simp [Finset.card_compl]
  omega


theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n))
    (hV1 : IsBisection n V1) (hW : IsBisection n W) :
    Rcard G V1 W ≤ 2 * (V1 ∩ W).card * dOut G V1 := by
  unfold Rcard
  have d1 : Disjoint (U1 V1 W) (W2 V1 W) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [U1, W2, Finset.mem_inter, Finset.mem_compl] at hx hx'
    tauto
  have d2 : Disjoint (U2 V1 W) (W1 V1 W) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [U2, W1, Finset.mem_sdiff, Finset.mem_compl] at hx hx'
    tauto
  rw [W_eb_eq G _ _ d1, W_eb_comm G (W1 V1 W) (U2 V1 W), W_eb_eq G _ _ d2]
  have h1 : ∑ a ∈ U1 V1 W, ((W2 V1 W).filter (fun b => G.Adj a b)).card ≤
      ∑ a ∈ U1 V1 W, dOut G V1 := by
    apply Finset.sum_le_sum
    apply W_outdeg G V1 (U1 V1 W) (W2 V1 W)
    intro a ha b hb
    simp only [U1, W2, Finset.mem_inter, Finset.mem_compl, sameSide] at ha hb ⊢
    tauto
  have h2 : ∑ a ∈ U2 V1 W, ((W1 V1 W).filter (fun b => G.Adj a b)).card ≤
      ∑ a ∈ U2 V1 W, dOut G V1 := by
    apply Finset.sum_le_sum
    apply W_outdeg G V1 (U2 V1 W) (W1 V1 W)
    intro a ha b hb
    simp only [U2, W1, Finset.mem_sdiff, Finset.mem_compl, sameSide] at ha hb ⊢
    tauto
  rw [Finset.sum_const, smul_eq_mul] at h1 h2
  have hc1 : (U1 V1 W).card = (V1 ∩ W).card := rfl
  have hc2 := W_U2card V1 W hV1 hW
  rw [hc1] at h1
  rw [hc2] at h2
  calc _ ≤ (V1 ∩ W).card * dOut G V1 + (V1 ∩ W).card * dOut G V1 := Nat.add_le_add h1 h2
    _ = 2 * (V1 ∩ W).card * dOut G V1 := by ring
