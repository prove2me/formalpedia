-- Prove2me | solution 1 for LPCommunity.MinBisect.two_t_dIn_le_S
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:00:56.053635+00:00
-- url     : https://prove2.me/submissions/26f2505f-f064-41b9-a5a7-8515763d6750

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

theorem W_eb_add_left {n : ℕ} (G : SimpleGraph (Fin n)) (A A' B : Finset (Fin n))
    (hAA' : Disjoint A A') (hAB : Disjoint A B) (hA'B : Disjoint A' B) :
    edgesBetween G (A ∪ A') B = edgesBetween G A B + edgesBetween G A' B := by
  rw [W_eb_eq G _ _ (Finset.disjoint_union_left.mpr ⟨hAB, hA'B⟩), W_eb_eq G _ _ hAB,
    W_eb_eq G _ _ hA'B, Finset.sum_union hAA']

theorem W_eb_add_right {n : ℕ} (G : SimpleGraph (Fin n)) (A B B' : Finset (Fin n))
    (hBB' : Disjoint B B') (hAB : Disjoint A B) (hAB' : Disjoint A B') :
    edgesBetween G A (B ∪ B') = edgesBetween G A B + edgesBetween G A B' := by
  rw [W_eb_comm G A (B ∪ B'), W_eb_comm G A B, W_eb_comm G A B']
  exact W_eb_add_left G B B' A hBB' hAB.symm hAB'.symm

theorem W_cut_eq {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    cutCost G S = edgesBetween G S Sᶜ := by
  unfold cutCost edgesBetween
  congr 1
  apply Finset.filter_congr
  intro p _
  simp only [sameSide, Finset.mem_compl]
  tauto

theorem W_disj_aux {n : ℕ} (V1 W : Finset (Fin n)) :
    Disjoint (U1 V1 W) (W1 V1 W) ∧ Disjoint (U1 V1 W) (U2 V1 W) ∧ Disjoint (U1 V1 W) (W2 V1 W) ∧
    Disjoint (W1 V1 W) (U2 V1 W) ∧ Disjoint (W1 V1 W) (W2 V1 W) ∧ Disjoint (U2 V1 W) (W2 V1 W) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [U1, U2, W1, W2, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_compl] at hx hx'
    tauto

theorem W_cut_decomp {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n)) :
    cutCost G V1 = Rcard G V1 W + edgesBetween G (U1 V1 W) (U2 V1 W) +
        edgesBetween G (W1 V1 W) (W2 V1 W) ∧
    cutCost G W = Scard G V1 W + edgesBetween G (U1 V1 W) (U2 V1 W) +
        edgesBetween G (W1 V1 W) (W2 V1 W) := by
  obtain ⟨d12, d13, d14, d23, d24, d34⟩ := W_disj_aux V1 W
  -- d12 : U1 W1, d13 : U1 U2, d14 : U1 W2, d23 : W1 U2, d24 : W1 W2, d34 : U2 W2
  have eV : V1 = U1 V1 W ∪ W1 V1 W := by
    ext x; simp only [U1, W1, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have eVc : V1ᶜ = W2 V1 W ∪ U2 V1 W := by
    ext x; simp only [W2, U2, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_compl]; tauto
  have eW : W = U1 V1 W ∪ W2 V1 W := by
    ext x; simp only [U1, W2, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]; tauto
  have eWc : Wᶜ = W1 V1 W ∪ U2 V1 W := by
    ext x; simp only [W1, U2, Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]; tauto
  constructor
  · have key : edgesBetween G V1 V1ᶜ =
        edgesBetween G (U1 V1 W ∪ W1 V1 W) (W2 V1 W ∪ U2 V1 W) := by rw [← eV, ← eVc]
    rw [W_cut_eq, key]
    rw [W_eb_add_left G _ _ _ d12 (Finset.disjoint_union_right.mpr ⟨d14, d13⟩)
        (Finset.disjoint_union_right.mpr ⟨d24, d23⟩),
      W_eb_add_right G _ _ _ d34.symm d14 d13, W_eb_add_right G _ _ _ d34.symm d24 d23]
    unfold Rcard
    ring
  · have key : edgesBetween G W Wᶜ =
        edgesBetween G (U1 V1 W ∪ W2 V1 W) (W1 V1 W ∪ U2 V1 W) := by rw [← eW, ← eWc]
    rw [W_cut_eq, key]
    rw [W_eb_add_left G _ _ _ d14 (Finset.disjoint_union_right.mpr ⟨d12, d13⟩)
        (Finset.disjoint_union_right.mpr ⟨d24.symm, d34.symm⟩),
      W_eb_add_right G _ _ _ d23 d12 d13, W_eb_add_right G _ _ _ d23 d24.symm d34.symm]
    unfold Scard
    rw [W_eb_comm G (W2 V1 W) (W1 V1 W), W_eb_comm G (W2 V1 W) (U2 V1 W)]
    ring

theorem W_lower {n : ℕ} (G : SimpleGraph (Fin n)) (V1 X A B : Finset (Fin n))
    (hX : ∀ a ∈ X, ∀ u, sameSide V1 a u ↔ u ∈ X) (hXAB : X = A ∪ B) (hAB : Disjoint A B) :
    ∀ a ∈ A, (dIn G V1 : ℤ) - A.card + 1 ≤ ((B.filter (fun b => G.Adj a b)).card : ℤ) := by
  intro a ha
  have haX : a ∈ X := by rw [hXAB]; exact Finset.mem_union_left _ ha
  have hdin : dIn G V1 ≤ inDeg G V1 a := by
    unfold dIn
    rw [dif_pos ⟨a, Finset.mem_univ a⟩]
    exact Finset.inf'_le _ (Finset.mem_univ a)
  have hin : inDeg G V1 a = (X.filter (fun u => G.Adj a u)).card := by
    unfold inDeg
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hX a haX u]
    tauto
  have hsplit : (X.filter (fun u => G.Adj a u)).card =
      (A.filter (fun u => G.Adj a u)).card + (B.filter (fun u => G.Adj a u)).card := by
    rw [hXAB, Finset.filter_union, Finset.card_union_of_disjoint]
    exact Finset.disjoint_filter_filter hAB
  have hA : (A.filter (fun u => G.Adj a u)).card ≤ A.card - 1 := by
    have : (A.filter (fun u => G.Adj a u)) ⊆ A.erase a := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_erase]
      exact ⟨fun h => G.loopless.irrefl a (h ▸ hu.2), hu.1⟩
    calc _ ≤ (A.erase a).card := Finset.card_le_card this
      _ = A.card - 1 := Finset.card_erase_of_mem ha
  have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, ha⟩
  have h1 : (dIn G V1 : ℤ) ≤ (A.filter (fun u => G.Adj a u)).card + (B.filter (fun u => G.Adj a u)).card := by
    have := hin ▸ hdin
    rw [hsplit] at this
    exact_mod_cast this
  have h2 : ((A.filter (fun u => G.Adj a u)).card : ℤ) ≤ (A.card : ℤ) - 1 := by
    have h' : (A.filter (fun u => G.Adj a u)).card + 1 ≤ A.card := by omega
    have h'' := (Nat.cast_le (α := ℤ)).mpr h'
    push_cast at h''
    linarith
  linarith


theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n))
    (hV1 : IsBisection n V1) (hW : IsBisection n W) :
    2 * ((V1 ∩ W).card : ℤ) * ((dIn G V1 : ℤ) - (V1 ∩ W).card + 1) ≤ (Scard G V1 W : ℤ) := by
  obtain ⟨d12, d13, d14, d23, d24, d34⟩ := W_disj_aux V1 W
  have eV : V1 = U1 V1 W ∪ W1 V1 W := by
    ext x; simp only [U1, W1, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have eVc : V1ᶜ = U2 V1 W ∪ W2 V1 W := by
    ext x; simp only [W2, U2, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_compl]; tauto
  have hc2 := W_U2card V1 W hV1 hW
  have hc1 : (U1 V1 W).card = (V1 ∩ W).card := rfl
  have l1 : ∀ a ∈ U1 V1 W, (dIn G V1 : ℤ) - (V1 ∩ W).card + 1 ≤
      (((W1 V1 W).filter (fun b => G.Adj a b)).card : ℤ) := by
    intro a ha
    have := W_lower G V1 V1 (U1 V1 W) (W1 V1 W) (by intro a ha u; simp only [sameSide]; tauto) eV d12 a ha
    rwa [hc1] at this
  have l2 : ∀ a ∈ U2 V1 W, (dIn G V1 : ℤ) - (V1 ∩ W).card + 1 ≤
      (((W2 V1 W).filter (fun b => G.Adj a b)).card : ℤ) := by
    intro a ha
    have := W_lower G V1 V1ᶜ (U2 V1 W) (W2 V1 W)
      (by intro a ha u; simp only [sameSide, Finset.mem_compl] at ha ⊢; tauto) eVc d34 a ha
    rwa [hc2] at this
  have s1 : ((V1 ∩ W).card : ℤ) * ((dIn G V1 : ℤ) - (V1 ∩ W).card + 1) ≤
      (edgesBetween G (U1 V1 W) (W1 V1 W) : ℤ) := by
    rw [W_eb_eq G _ _ d12]
    push_cast
    calc ((V1 ∩ W).card : ℤ) * ((dIn G V1 : ℤ) - (V1 ∩ W).card + 1)
        = ∑ a ∈ U1 V1 W, ((dIn G V1 : ℤ) - (V1 ∩ W).card + 1) := by
          rw [Finset.sum_const, hc1, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum l1
  have s2 : ((V1 ∩ W).card : ℤ) * ((dIn G V1 : ℤ) - (V1 ∩ W).card + 1) ≤
      (edgesBetween G (U2 V1 W) (W2 V1 W) : ℤ) := by
    rw [W_eb_eq G _ _ d34]
    push_cast
    calc ((V1 ∩ W).card : ℤ) * ((dIn G V1 : ℤ) - (V1 ∩ W).card + 1)
        = ∑ a ∈ U2 V1 W, ((dIn G V1 : ℤ) - (V1 ∩ W).card + 1) := by
          rw [Finset.sum_const, hc2, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum l2
  unfold Scard
  push_cast
  linarith
