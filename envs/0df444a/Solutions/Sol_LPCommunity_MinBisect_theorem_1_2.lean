-- Prove2me | solution 2 for LPCommunity.MinBisect.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:24.245657+00:00
-- url     : https://prove2.me/submissions/59e1ff50-9f42-453a-88a6-8f72fdf803e0

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting
import Theorems.Thm_LPCommunity_MinBisect_R_le_two_t_dOut
import Theorems.Thm_LPCommunity_MinBisect_two_t_dIn_le_S

-- carved verbatim out of submission 79ef1807-dd5f-4e83-8d8e-c0ac7d278426, lines 355-376

section
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

theorem W_S_le {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n))
    (hV1 : IsBisection n V1) (hW : IsBisection n W)
    (hopt : ∀ S : Finset (Fin n), IsBisection n S → cutCost G W ≤ cutCost G S) :
    Scard G V1 W ≤ Rcard G V1 W := by
  obtain ⟨h1, h2⟩ := W_cut_decomp G V1 W
  have := hopt V1 hV1
  omega

theorem W_key {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n))
    (hV1 : IsBisection n V1) (hW : IsBisection n W)
    (hopt : ∀ S : Finset (Fin n), IsBisection n S → cutCost G W ≤ cutCost G S)
    (h4 : (n : ℤ) < 4 * ((dIn G V1 : ℤ) - (dOut G V1 : ℤ)) + 4)
    (ht : 0 < (V1 ∩ W).card) : (n : ℤ) < 4 * ((V1 ∩ W).card : ℤ) := by
  have h1 := LPCommunity.MinBisect.two_t_dIn_le_S G V1 W hV1 hW
  have h2 := W_S_le G V1 W hV1 hW hopt
  have h3 := LPCommunity.MinBisect.R_le_two_t_dOut G V1 W hV1 hW
  have h2' : (Scard G V1 W : ℤ) ≤ (Rcard G V1 W : ℤ) := by exact_mod_cast h2
  have h3' : (Rcard G V1 W : ℤ) ≤ 2 * ((V1 ∩ W).card : ℤ) * (dOut G V1 : ℤ) := by exact_mod_cast h3
  have htz : (0 : ℤ) < ((V1 ∩ W).card : ℤ) := by exact_mod_cast ht
  have hmul : 2 * ((V1 ∩ W).card : ℤ) * ((dIn G V1 : ℤ) - (V1 ∩ W).card + 1) ≤
      2 * ((V1 ∩ W).card : ℤ) * (dOut G V1 : ℤ) := by linarith
  have hle : (dIn G V1 : ℤ) - (V1 ∩ W).card + 1 ≤ (dOut G V1 : ℤ) :=
    le_of_mul_le_mul_left hmul (by linarith)
  linarith

theorem W_cut_compl {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) :
    cutCost G Wᶜ = cutCost G W := by
  rw [W_cut_eq, W_cut_eq, compl_compl, W_eb_comm]

theorem W_isb_compl {n : ℕ} (W : Finset (Fin n)) (hW : IsBisection n W) : IsBisection n Wᶜ := by
  unfold IsBisection at *
  have : Wᶜ.card = n - W.card := by simp [Finset.card_compl]
  omega

theorem W_minimizer {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n))
    (hV1 : IsBisection n V1) (h4 : (n : ℤ) < 4 * ((dIn G V1 : ℤ) - (dOut G V1 : ℤ)) + 4)
    (W : Finset (Fin n)) (hW : IsBisection n W)
    (hopt : ∀ S : Finset (Fin n), IsBisection n S → cutCost G W ≤ cutCost G S) :
    W = V1 ∨ W = V1ᶜ := by
  have hWc := W_isb_compl W hW
  have hoptc : ∀ S : Finset (Fin n), IsBisection n S → cutCost G Wᶜ ≤ cutCost G S := by
    intro S hS; rw [W_cut_compl]; exact hopt S hS
  unfold IsBisection at hV1 hW hWc
  have hsplit : (V1 ∩ W).card + (V1 ∩ Wᶜ).card = V1.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]; tauto
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_inter, Finset.mem_compl] at hx hx'
      tauto
  by_cases ht : (V1 ∩ W).card = 0
  · right
    have hdisj : W ⊆ V1ᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hx1
      have : x ∈ V1 ∩ W := Finset.mem_inter.mpr ⟨hx1, hx⟩
      rw [Finset.card_eq_zero] at ht
      rw [ht] at this
      simp at this
    have hc : V1ᶜ.card = n - V1.card := by simp [Finset.card_compl]
    exact Finset.eq_of_subset_of_card_le hdisj (by omega)
  by_cases ht' : (V1 ∩ Wᶜ).card = 0
  · left
    have hsub : V1 ⊆ W := by
      intro x hx
      by_contra hxW
      have : x ∈ V1 ∩ Wᶜ := Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxW⟩
      rw [Finset.card_eq_zero] at ht'
      rw [ht'] at this
      simp at this
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  exfalso
  have k1 := W_key G V1 W hV1 hW hopt h4 (Nat.pos_of_ne_zero ht)
  have k2 := W_key G V1 Wᶜ hV1 hWc hoptc h4 (Nat.pos_of_ne_zero ht')
  have : ((V1 ∩ W).card : ℤ) + (V1 ∩ Wᶜ).card = V1.card := by exact_mod_cast hsplit
  have hn : (2 * V1.card : ℤ) = n := by exact_mod_cast hV1
  linarith

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)) (hV1 : IsBisection n V1)
    (h : (dIn G V1 : ℝ) - (dOut G V1 : ℝ) > (n : ℝ) / 4 - 1) :
    MinBisectRecovers G V1 := by
  have h4 : (n : ℤ) < 4 * ((dIn G V1 : ℤ) - (dOut G V1 : ℤ)) + 4 := by
    have : (n : ℝ) < 4 * ((dIn G V1 : ℝ) - (dOut G V1 : ℝ)) + 4 := by linarith
    exact_mod_cast this
  -- existence of a global minimizer
  obtain ⟨W0, hW0mem, hW0min⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun S : Finset (Fin n) => IsBisection n S)) (cutCost G) ⟨V1, by simp [hV1]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW0mem hW0min
  have hcase := W_minimizer G V1 hV1 h4 W0 hW0mem hW0min
  have hV1min : cutCost G W0 = cutCost G V1 := by
    rcases hcase with rfl | rfl
    · rfl
    · exact W_cut_compl G V1
  intro S hS hSle
  apply W_minimizer G V1 hV1 h4 S hS
  intro S' hS'
  calc cutCost G S ≤ cutCost G V1 := hSle
    _ = cutCost G W0 := hV1min.symm
    _ ≤ cutCost G S' := hW0min S' hS'

end
