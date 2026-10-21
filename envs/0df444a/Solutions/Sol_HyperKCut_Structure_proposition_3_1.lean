-- Prove2me | solution 1 for HyperKCut.Structure.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:24:58.782889+00:00
-- url     : https://prove2.me/submissions/0840dbaa-11c5-4403-acd2-844ef881eee7

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

open HyperKCut.Structure
namespace HKYWZAux

variable {V : Type} [Fintype V] [DecidableEq V]

theorem snoc2_cases {p : ℕ} (Y : Fin p → Finset V) (W Z : Finset V)
    (q : Finset V → Prop) (i : Fin (p + 2))
    (hY : ∀ j, q (Y j)) (hW : q W) (hZ : q Z) :
    q (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z i) := by
  induction i using Fin.lastCases with
  | last => simpa using hZ
  | cast i =>
    rw [Fin.snoc_castSucc]
    induction i using Fin.lastCases with
    | last => simpa using hW
    | cast i => rw [Fin.snoc_castSucc]; exact hY i

/-- Basic facts about a partition `(Y₁,…,Yₚ,W,Z)`. -/
theorem ywz_facts {p : ℕ} (Y : Fin p → Finset V) (W Z : Finset V)
    (h : IsPartitionYWZ Y W Z) :
    (∀ i, (Y i).Nonempty) ∧ W.Nonempty ∧ Z.Nonempty ∧
    (∀ i j, i ≠ j → Disjoint (Y i) (Y j)) ∧
    (∀ i, Disjoint (Y i) W) ∧ (∀ i, Disjoint (Y i) Z) ∧ Disjoint W Z ∧
    (∀ v, (∃ i, v ∈ Y i) ∨ v ∈ W ∨ v ∈ Z) := by
  obtain ⟨hne, hdis, hcov⟩ := h
  have eY : ∀ i, Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.castSucc (Fin.castSucc i)) = Y i := by intro i; simp
  have eW : Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.castSucc (Fin.last p)) = W := by simp
  have eZ : Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z
      (Fin.last (p + 1)) = Z := by simp
  refine ⟨fun i => ?_, ?_, ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_, ?_, fun v => ?_⟩
  · have := hne (Fin.castSucc (Fin.castSucc i)); rwa [eY] at this
  · have := hne (Fin.castSucc (Fin.last p)); rwa [eW] at this
  · have := hne (Fin.last (p + 1)); rwa [eZ] at this
  · have := hdis (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.castSucc j))
      (fun h => hij (Fin.castSucc_injective _ (Fin.castSucc_injective _ h)))
    rwa [eY, eY] at this
  · have := hdis (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.last p))
      (fun h => (Fin.castSucc_lt_last i).ne (Fin.castSucc_injective _ h))
    rwa [eY, eW] at this
  · have := hdis (Fin.castSucc (Fin.castSucc i)) (Fin.last (p + 1))
      (Fin.castSucc_lt_last _).ne
    rwa [eY, eZ] at this
  · have := hdis (Fin.castSucc (Fin.last p)) (Fin.last (p + 1)) (Fin.castSucc_lt_last _).ne
    rwa [eW, eZ] at this
  · obtain ⟨i, hi⟩ := hcov v
    revert hi
    induction i using Fin.lastCases with
    | last => intro hi; right; right; simpa using hi
    | cast i =>
      rw [Fin.snoc_castSucc]
      induction i using Fin.lastCases with
      | last => intro hi; right; left; simpa using hi
      | cast i => rw [Fin.snoc_castSucc]; intro hi; left; exact ⟨i, hi⟩

end HKYWZAux

namespace HKSigAux

variable {V : Type} [Fintype V] [DecidableEq V]

theorem card_filter_eq_sum {W : Type} (E : Multiset (Finset W)) (q : Finset W → Prop)
    [DecidablePred q] :
    (E.filter q).card = (E.map (fun e => if q e then 1 else 0)).sum := by
  induction E using Multiset.induction_on with
  | empty => simp
  | cons a E ih =>
    simp only [Multiset.filter_cons, Multiset.map_cons, Multiset.sum_cons]
    split_ifs <;> simp [ih] <;> omega

/-- Per-edge contribution to σ, in terms of the number of `Y`-parts met and whether `W`, `Z`
are met. -/
def sigB (n : ℕ) (w z : Bool) : ℕ :=
  (if 2 ≤ n + w.toNat + z.toNat then 1 else 0) +
  (if n = 0 ∧ w = true ∧ z = true then 1 else 0) +
  (if z = true ∧ (2 ≤ n ∨ (1 ≤ n ∧ w = true)) then 1 else 0) +
  (if z = false ∧ 2 ≤ n then 1 else 0)

theorem numParts_eq {p : ℕ} (Y : Fin p → Finset V) (W Z e : Finset V) :
    (Finset.univ.filter (fun o : Fin (p + 2) => Meets e
      (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z o))).card =
    numYMet e Y + (decide (Meets e W)).toNat + (decide (Meets e Z)).toNat := by
  unfold numYMet
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  by_cases hW : Meets e W <;> by_cases hZ : Meets e Z <;> simp [hW, hZ]

theorem old_iff {p : ℕ} (Y : Fin p → Finset V) (W Z e : Finset V) :
    (∃ i j, i ≠ j ∧
      Meets e (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z i) ∧
      Meets e (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z j)) ↔
    2 ≤ numYMet e Y + (decide (Meets e W)).toNat + (decide (Meets e Z)).toNat := by
  rw [← numParts_eq]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    have : 1 < (Finset.univ.filter (fun o : Fin (p + 2) => Meets e
      (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z o))).card :=
      Finset.one_lt_card.mpr ⟨i, by simpa using hi, j, by simpa using hj, hij⟩
    omega
  · intro h
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter
      (fun o : Fin (p + 2) => Meets e
      (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z o))).card)
    exact ⟨i, j, hij, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩

theorem numYMet_eq_zero {p : ℕ} (Y : Fin p → Finset V) (e : Finset V) :
    numYMet e Y = 0 ↔ ∀ i, ¬ Meets e (Y i) := by
  unfold numYMet
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp

theorem sigma_eq {p : ℕ} (H : HyperKCut.Structure.Hypergraph V) (Y : Fin p → Finset V)
    (W Z : Finset V) (hP : IsPartitionYWZ Y W Z) :
    sigma H Y W Z =
      (H.edges.map (fun e => sigB (numYMet e Y) (decide (Meets e W)) (decide (Meets e Z)))).sum := by
  classical
  obtain ⟨_, _, _, _, hYW, hYZ, _, hcov⟩ := HKYWZAux.ywz_facts Y W Z hP
  unfold sigma costYWZ cost costWZ alpha beta
  rw [card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum,
    ← Multiset.sum_map_add, ← Multiset.sum_map_add, ← Multiset.sum_map_add]
  congr 1
  apply Multiset.map_congr rfl
  intro e _
  unfold sigB
  have h1 := old_iff Y W Z e
  have h2 : (e ⊆ W ∪ Z ∧ Meets e W ∧ Meets e Z) ↔
      (numYMet e Y = 0 ∧ decide (Meets e W) = true ∧ decide (Meets e Z) = true) := by
    rw [numYMet_eq_zero]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hsub, hw, hz⟩
      refine ⟨fun i ⟨v, hv⟩ => ?_, hw, hz⟩
      rw [Finset.mem_inter] at hv
      rcases Finset.mem_union.mp (hsub hv.1) with h | h
      · exact Finset.disjoint_left.mp (hYW i) hv.2 h
      · exact Finset.disjoint_left.mp (hYZ i) hv.2 h
    · rintro ⟨hn, hw, hz⟩
      refine ⟨fun v hv => ?_, hw, hz⟩
      rcases hcov v with ⟨i, hi⟩ | h | h
      · exact absurd ⟨v, Finset.mem_inter.mpr ⟨hv, hi⟩⟩ (hn i)
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ h
  by_cases c1 : ∃ i j, i ≠ j ∧
      Meets e (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z i) ∧
      Meets e (Fin.snoc (α := fun _ => Finset V) (Fin.snoc (α := fun _ => Finset V) Y W) Z j)
  · rw [if_pos c1, if_pos (h1.mp c1)]
    by_cases c2 : e ⊆ W ∪ Z ∧ Meets e W ∧ Meets e Z
    · rw [if_pos c2, if_pos (h2.mp c2)]
      by_cases hw : Meets e W <;> by_cases hz : Meets e Z <;> simp [hw, hz]
    · rw [if_neg c2, if_neg (fun h => c2 (h2.mpr h))]
      by_cases hw : Meets e W <;> by_cases hz : Meets e Z <;> simp [hw, hz]
  · rw [if_neg c1, if_neg (fun h => c1 (h1.mpr h))]
    by_cases c2 : e ⊆ W ∪ Z ∧ Meets e W ∧ Meets e Z
    · rw [if_pos c2, if_pos (h2.mp c2)]
      by_cases hw : Meets e W <;> by_cases hz : Meets e Z <;> simp [hw, hz]
    · rw [if_neg c2, if_neg (fun h => c2 (h2.mpr h))]
      by_cases hw : Meets e W <;> by_cases hz : Meets e Z <;> simp [hw, hz]

end HKSigAux

theorem HKP31_meets_union {V : Type} [DecidableEq V] (e A B : Finset V) :
    Meets e (A ∪ B) ↔ Meets e A ∨ Meets e B := by
  unfold Meets
  rw [Finset.inter_union_distrib_left, Finset.union_nonempty]

open HKYWZAux HKSigAux in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : HyperKCut.Structure.Hypergraph V)
    (Y₁ Y₂ W Z : Finset V)
    (hP : IsPartitionYWZ ![Y₁, Y₂] W Z) :
    d H (Y₁ ∪ W) + d H (Y₂ ∪ W) = sigma H ![Y₁, Y₂] W Z := by
  classical
  obtain ⟨_, _, _, hYY, hYW, hYZ, hWZ, hcov⟩ := ywz_facts _ W Z hP
  have hY0 : (![Y₁, Y₂] : Fin 2 → Finset V) 0 = Y₁ := rfl
  have hY1 : (![Y₁, Y₂] : Fin 2 → Finset V) 1 = Y₂ := rfl
  have d12 : Disjoint Y₁ Y₂ := by
    have := hYY 0 1 (by decide); rwa [hY0, hY1] at this
  have c1 : (Y₁ ∪ W)ᶜ = Y₂ ∪ Z := by
    ext v
    simp only [Finset.mem_compl, Finset.mem_union]
    constructor
    · intro h
      rcases hcov v with ⟨i, hi⟩ | h' | h'
      · fin_cases i
        · exact absurd (Or.inl hi) h
        · exact Or.inl hi
      · exact absurd (Or.inr h') h
      · exact Or.inr h'
    · rintro (h | h) (h' | h')
      · exact Finset.disjoint_left.mp d12 h' h
      · exact Finset.disjoint_left.mp (by have := hYW 1; rwa [hY1] at this) h h'
      · exact Finset.disjoint_left.mp (by have := hYZ 0; rwa [hY0] at this) h' h
      · exact Finset.disjoint_left.mp hWZ h' h
  have c2 : (Y₂ ∪ W)ᶜ = Y₁ ∪ Z := by
    ext v
    simp only [Finset.mem_compl, Finset.mem_union]
    constructor
    · intro h
      rcases hcov v with ⟨i, hi⟩ | h' | h'
      · fin_cases i
        · exact Or.inl hi
        · exact absurd (Or.inl hi) h
      · exact absurd (Or.inr h') h
      · exact Or.inr h'
    · rintro (h | h) (h' | h')
      · exact Finset.disjoint_left.mp d12 h h'
      · exact Finset.disjoint_left.mp (by have := hYW 0; rwa [hY0] at this) h h'
      · exact Finset.disjoint_left.mp (by have := hYZ 1; rwa [hY1] at this) h' h
      · exact Finset.disjoint_left.mp hWZ h' h
  rw [sigma_eq H _ W Z hP]
  unfold d
  rw [c1, c2, card_filter_eq_sum, card_filter_eq_sum, ← Multiset.sum_map_add]
  congr 1
  apply Multiset.map_congr rfl
  intro e _
  have hn : numYMet e ![Y₁, Y₂] = (decide (Meets e Y₁)).toNat + (decide (Meets e Y₂)).toNat := by
    unfold numYMet
    rw [Finset.card_filter, Fin.sum_univ_two, hY0, hY1]
    by_cases a : Meets e Y₁ <;> by_cases b : Meets e Y₂ <;> simp [a, b]
  rw [hn]
  simp only [HKP31_meets_union]
  unfold sigB
  by_cases a : Meets e Y₁ <;> by_cases b : Meets e Y₂ <;> by_cases w : Meets e W <;>
    by_cases z : Meets e Z <;> simp [a, b, w, z]
