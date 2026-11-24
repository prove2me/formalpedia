-- Prove2me | solution 1 for IntervalMaxCutEPTAS.Scheme.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:05:02.402478+00:00
-- url     : https://prove2.me/submissions/99a8c627-b122-476c-80c6-6b6a55e39d43

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Graph

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntervalMaxCutEPTAS.Scheme

/-- The ordered adjacent pairs are twice the edges. -/
private lemma card_adj_pairs {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ((Finset.univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2)).card =
      2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges, Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, Finset.card_filter]

/-- `cutCount` as a sum over ordered adjacent pairs. -/
private lemma cutCount_eq_sum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    cutCount G S = ∑ p ∈ (Finset.univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
      if p.1 ∈ S ∧ p.2 ∉ S then 1 else 0 := by
  rw [← Finset.card_filter]
  unfold cutCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl, Finset.mem_univ, true_and]
  tauto

/-- Number of `(k+1)`-sets containing `x` and avoiding `y`. -/
private lemma count_sep {V : Type} [Fintype V] [DecidableEq V] (x y : V) (hxy : x ≠ y) (k : ℕ) :
    (((Finset.univ : Finset V).powersetCard (k + 1)).filter (fun S => x ∈ S ∧ y ∉ S)).card =
      (Fintype.card V - 2).choose k := by
  set T := ((Finset.univ : Finset V).erase x).erase y with hT
  have hTc : T.card = Fintype.card V - 2 := by
    rw [hT, Finset.card_erase_of_mem (by simp [hxy.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    omega
  have hTx : x ∉ T := by simp [hT]
  have hTy : y ∉ T := by simp [hT]
  have heq : ((Finset.univ : Finset V).powersetCard (k + 1)).filter (fun S => x ∈ S ∧ y ∉ S) =
      (T.powersetCard k).image (insert x) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image, Finset.subset_univ,
      true_and]
    constructor
    · rintro ⟨hS, hx, hy⟩
      refine ⟨S.erase x, ⟨?_, ?_⟩, Finset.insert_erase hx⟩
      · intro z hz
        rw [Finset.mem_erase] at hz
        rw [hT, Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun h => hy (h ▸ hz.2), hz.1, Finset.mem_univ z⟩
      · rw [Finset.card_erase_of_mem hx, hS]
        rfl
    · rintro ⟨R, ⟨hR, hRc⟩, rfl⟩
      have hxR : x ∉ R := fun h => hTx (hR h)
      have hyR : y ∉ R := fun h => hTy (hR h)
      refine ⟨?_, Finset.mem_insert_self x R, ?_⟩
      · rw [Finset.card_insert_of_notMem hxR, hRc]
      · rw [Finset.mem_insert, not_or]
        exact ⟨hxy.symm, hyR⟩
  rw [heq, Finset.card_image_of_injOn, Finset.card_powersetCard, hTc]
  intro R1 hR1 R2 hR2 h
  have hx1 : x ∉ R1 := fun hh => hTx ((Finset.mem_powersetCard.mp hR1).1 hh)
  have hx2 : x ∉ R2 := fun hh => hTx ((Finset.mem_powersetCard.mp hR2).1 hh)
  rw [← Finset.erase_insert hx1, ← Finset.erase_insert hx2]
  exact congrArg (fun R => Finset.erase R x) h

/-- `C(m+2, k+1) ≤ 4 C(m, k)` when `k + 1 = ⌊(m+2)/2⌋`. -/
private lemma binom_ineq (m k : ℕ) (hk : (m + 2) / 2 = k + 1) :
    (m + 2).choose (k + 1) ≤ 4 * m.choose k := by
  have i1 : (m + 2) * (m + 1).choose k = (m + 2).choose (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (m + 1) k
  have i2 : m.choose k * (m + 1) = (m + 1).choose k * (m + 1 - k) := Nat.choose_mul_succ_eq m k
  generalize (m + 2).choose (k + 1) = A at i1 ⊢
  generalize (m + 1).choose k = B at i1 i2
  generalize m.choose k = C at i2 ⊢
  obtain ⟨j, hj⟩ : ∃ j, m + 1 - k = j := ⟨_, rfl⟩
  rw [hj] at i2
  have hj4 : (m + 2) * (m + 1) ≤ 4 * ((k + 1) * j) := by
    rcases (by omega : (m = 2 * k ∧ j = k + 1) ∨ (m = 2 * k + 1 ∧ j = k + 2)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> nlinarith
  have hjpos : 0 < (k + 1) * j := Nat.mul_pos (Nat.succ_pos k) (by omega)
  have e : A * ((k + 1) * j) = (m + 2) * (m + 1) * C := by
    calc A * ((k + 1) * j) = (A * (k + 1)) * j := by ring
      _ = (m + 2) * (B * j) := by rw [← i1]; ring
      _ = (m + 2) * (C * (m + 1)) := by rw [i2]
      _ = (m + 2) * (m + 1) * C := by ring
  apply Nat.le_of_mul_le_mul_right _ hjpos
  rw [e]
  calc (m + 2) * (m + 1) * C ≤ 4 * ((k + 1) * j) * C := Nat.mul_le_mul_right _ hj4
    _ = 4 * C * ((k + 1) * j) := by ring

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ 2 * mc G ∧
      (2 ≤ Fintype.card V → G.edgeFinset.card ≤ 2 * mb G) := by
  have key : 2 ≤ Fintype.card V → G.edgeFinset.card ≤ 2 * mb G := by
    intro hn
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card V / 2 = k + 1 := ⟨Fintype.card V / 2 - 1, by omega⟩
    set D := (Finset.univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2) with hD
    set P := (Finset.univ : Finset (Finset V)).filter
      (fun S => S.card = Fintype.card V / 2) with hP
    have hP' : P = (Finset.univ : Finset V).powersetCard (k + 1) := by
      ext S
      simp [hP, Finset.mem_powersetCard, hk]
    have h1 : ∑ S ∈ P, cutCount G S ≤ P.card * mb G := by
      have := Finset.sum_le_card_nsmul P (cutCount G) (mb G) (fun S hS => by
        unfold mb
        exact Finset.le_sup (f := cutCount G) hS)
      simpa using this
    have h2 : ∑ S ∈ P, cutCount G S = D.card * (Fintype.card V - 2).choose k := by
      simp_rw [cutCount_eq_sum]
      rw [← hD, Finset.sum_comm, Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [← Finset.card_filter, hP']
      rw [hD, Finset.mem_filter] at hp
      exact count_sep p.1 p.2 hp.2.ne k
    have h3 : D.card = 2 * G.edgeFinset.card := card_adj_pairs G
    have h4 : P.card = (Fintype.card V).choose (k + 1) := by
      rw [hP', Finset.card_powersetCard, Finset.card_univ]
    have h5 : (Fintype.card V).choose (k + 1) ≤ 4 * (Fintype.card V - 2).choose k := by
      have e : Fintype.card V = (Fintype.card V - 2) + 2 := by omega
      have := binom_ineq (Fintype.card V - 2) k (by rw [← e]; exact hk)
      rwa [← e] at this
    have h6 : 0 < (Fintype.card V).choose (k + 1) := Nat.choose_pos (by omega)
    set E := G.edgeFinset.card
    set N := (Fintype.card V - 2).choose k
    set Cn := (Fintype.card V).choose (k + 1)
    rw [h4] at h1
    rw [h2, h3] at h1
    apply Nat.le_of_mul_le_mul_right _ h6
    calc E * Cn ≤ E * (4 * N) := Nat.mul_le_mul_left _ h5
      _ = 2 * (2 * E * N) := by ring
      _ ≤ 2 * (Cn * mb G) := Nat.mul_le_mul_left _ h1
      _ = 2 * mb G * Cn := by ring
  refine ⟨?_, key⟩
  by_cases hn : 2 ≤ Fintype.card V
  · refine (key hn).trans (Nat.mul_le_mul_left _ ?_)
    unfold mb mc
    exact Finset.sup_mono (Finset.filter_subset _ _)
  · have : G.edgeFinset.card ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
    rw [Nat.choose_eq_zero_of_lt (by omega)] at this
    omega
