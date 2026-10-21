-- Prove2me | solution 1 for HyperKCut.Structure.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:41:45.094737+00:00
-- url     : https://prove2.me/submissions/7958c30d-3585-4515-af9f-f93d1af605ac

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Theorems.Thm_HyperKCut_Structure_lemma_3_1
import Theorems.Thm_HyperKCut_Structure_proposition_3_1

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


namespace HKL31Aux
open HKSigAux HKYWZAux

variable {V : Type} [Fintype V] [DecidableEq V]

theorem meets_iff (e A : Finset V) : Meets e A ↔ ∃ v, v ∈ e ∧ v ∈ A := by
  unfold Meets
  constructor
  · rintro ⟨v, hv⟩; rw [Finset.mem_inter] at hv; exact ⟨v, hv⟩
  · rintro ⟨v, h1, h2⟩; exact ⟨v, Finset.mem_inter.mpr ⟨h1, h2⟩⟩

theorem one_le_numYMet {p : ℕ} (Y : Fin p → Finset V) (e : Finset V) :
    1 ≤ numYMet e Y ↔ ∃ i, Meets e (Y i) := by
  have := numYMet_eq_zero Y e
  constructor
  · intro h; by_contra hc; push_neg at hc; have := this.mpr hc; omega
  · rintro ⟨i, hi⟩; by_contra hc; exact this.mp (by omega) i hi

theorem numYMet_sum {p : ℕ} (Y : Fin p → Finset V) (e : Finset V) :
    numYMet e Y = ∑ i, if Meets e (Y i) then 1 else 0 := by
  unfold numYMet; rw [Finset.card_filter]

/-- Building a `(Y,W,Z)` partition from its elementary facts. -/
theorem ywz_mk {p : ℕ} (Y : Fin p → Finset V) (W Z : Finset V)
    (hYn : ∀ i, (Y i).Nonempty) (hWn : W.Nonempty) (hZn : Z.Nonempty)
    (hYY : ∀ i j, i ≠ j → Disjoint (Y i) (Y j))
    (hYW : ∀ i, Disjoint (Y i) W) (hYZ : ∀ i, Disjoint (Y i) Z) (hWZ : Disjoint W Z)
    (hcov : ∀ v, (∃ i, v ∈ Y i) ∨ v ∈ W ∨ v ∈ Z) :
    IsPartitionYWZ Y W Z := by
  refine ⟨fun i => snoc2_cases Y W Z (fun s => s.Nonempty) i hYn hWn hZn, ?_, ?_⟩
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j =>
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        induction j using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hWZ.symm
        | cast j => rw [Fin.snoc_castSucc]; exact (hYZ j).symm
    | cast i =>
      rw [Fin.snoc_castSucc]
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last]
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hWZ
        | cast i => rw [Fin.snoc_castSucc]; exact hYZ i
      | cast j =>
        rw [Fin.snoc_castSucc]
        have hij' : i ≠ j := fun h => hij (by rw [h])
        induction i using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last]
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij'
          | cast j => rw [Fin.snoc_castSucc]; exact (hYW j).symm
        | cast i =>
          rw [Fin.snoc_castSucc]
          induction j using Fin.lastCases with
          | last => rw [Fin.snoc_last]; exact hYW i
          | cast j =>
            rw [Fin.snoc_castSucc]
            exact hYY i j (fun h => hij' (by rw [h]))
  · intro v
    rcases hcov v with ⟨i, hi⟩ | h | h
    · exact ⟨Fin.castSucc (Fin.castSucc i), by simpa using hi⟩
    · exact ⟨Fin.castSucc (Fin.last p), by simpa using h⟩
    · exact ⟨Fin.last (p + 1), by simpa using h⟩

theorem d_eq_sum (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) :
    d H A = (H.edges.map (fun e => if Meets e A ∧ Meets e Aᶜ then 1 else 0)).sum := by
  unfold d; rw [card_filter_eq_sum]

end HKL31Aux

namespace HKL32Aux
open HKSigAux HKYWZAux

variable {V : Type} [Fintype V] [DecidableEq V]

def Zs {p : ℕ} (A : Fin p → Finset V) : Finset V := Finset.univ.filter (fun v => ∀ i, v ∉ A i)
def Ws {p : ℕ} (A : Fin p → Finset V) : Finset V := Finset.univ.filter
  (fun v => ∃ i j : Fin p, i ≠ j ∧ v ∈ A i ∧ v ∈ A j)
def Ys {p : ℕ} (A : Fin p → Finset V) : Fin p → Finset V := fun i => A i \ Ws A

theorem mem_Zs {p : ℕ} (A : Fin p → Finset V) (v : V) : v ∈ Zs A ↔ ∀ i, v ∉ A i := by
  simp [Zs]
theorem mem_Ws {p : ℕ} (A : Fin p → Finset V) (v : V) :
    v ∈ Ws A ↔ ∃ i j : Fin p, i ≠ j ∧ v ∈ A i ∧ v ∈ A j := by
  simp [Ws]

/-- The hypotheses of Lemma 3.2. -/
def Good (H : HyperKCut.Structure.Hypergraph V) (p : ℕ) (R U : Finset V) (u : Fin p → V)
    (A : Fin p → Finset V) : Prop :=
  R.Nonempty ∧ R ⊂ U ∧ U ⊂ (Finset.univ : Finset V) ∧ Function.Injective u ∧
  (∀ i, u i ∈ U \ R) ∧
  (∀ i, IsMinTerminalCut H (((Finset.univ.image u) ∪ R).erase (u i)) Uᶜ (A i)ᶜ) ∧
  (∀ i, u i ∈ A i) ∧ (∀ i j, i ≠ j → u i ∉ A j)

theorem good_Uc {H : HyperKCut.Structure.Hypergraph V} {p : ℕ} {R U : Finset V} {u : Fin p → V}
    {A : Fin p → Finset V} (h : Good H p R U u A) (i : Fin p) (v : V) (hv : v ∉ U) :
    v ∈ A i := by
  obtain ⟨_, _, _, _, _, hA, _, _⟩ := h
  by_contra hc
  exact Finset.disjoint_left.mp (hA i).1.2 (Finset.mem_compl.mpr hc) (Finset.mem_compl.mpr hv)

theorem good_R {H : HyperKCut.Structure.Hypergraph V} {p : ℕ} {R U : Finset V} {u : Fin p → V}
    {A : Fin p → Finset V} (h : Good H p R U u A) (i : Fin p) (r : V) (hr : r ∈ R) :
    r ∉ A i := by
  obtain ⟨_, _, _, _, hu, hA, _, _⟩ := h
  have hne : r ≠ u i := by
    rintro rfl; exact (Finset.mem_sdiff.mp (hu i)).2 hr
  have : r ∈ ((Finset.univ.image u) ∪ R).erase (u i) :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_union_right _ hr⟩
  exact Finset.mem_compl.mp ((hA i).1.1 this)

theorem good_partition {H : HyperKCut.Structure.Hypergraph V} {p : ℕ} (hp : 2 ≤ p)
    {R U : Finset V} {u : Fin p → V}
    {A : Fin p → Finset V} (h : Good H p R U u A) : IsPartitionYWZ (Ys A) (Ws A) (Zs A) := by
  have hUc := good_Uc h
  have hRo := good_R h
  obtain ⟨hRn, _, hUV, _, _, _, hui, huj⟩ := h
  have huW : ∀ i, u i ∉ Ws A := by
    intro i hw
    obtain ⟨a, b, hab, ha, hb⟩ := (mem_Ws A _).mp hw
    by_cases hia : i = a
    · subst hia; exact huj i b (Ne.symm (Ne.symm hab)) hb
    · exact huj i a hia ha
  apply HKL31Aux.ywz_mk
  · intro i; exact ⟨u i, Finset.mem_sdiff.mpr ⟨hui i, huW i⟩⟩
  · obtain ⟨v, -, hv⟩ := Finset.exists_of_ssubset hUV
    refine ⟨v, (mem_Ws A v).mpr ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, hUc _ v hv, hUc _ v hv⟩⟩
    simp [Fin.ext_iff]
  · obtain ⟨r, hr⟩ := hRn
    exact ⟨r, (mem_Zs A r).mpr (fun i => hRo i r hr)⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro v hi hj
    exact (Finset.mem_sdiff.mp hi).2 ((mem_Ws A v).mpr
      ⟨i, j, hij, (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hj).1⟩)
  · intro i; exact Finset.sdiff_disjoint
  · intro i
    rw [Finset.disjoint_left]
    intro v hi hz
    exact (mem_Zs A v).mp hz i (Finset.mem_sdiff.mp hi).1
  · rw [Finset.disjoint_left]
    intro v hw hz
    obtain ⟨a, _, _, ha, _⟩ := (mem_Ws A v).mp hw
    exact (mem_Zs A v).mp hz a ha
  · intro v
    by_cases hw : v ∈ Ws A
    · exact Or.inr (Or.inl hw)
    · by_cases hz : ∀ i, v ∉ A i
      · exact Or.inr (Or.inr ((mem_Zs A v).mpr hz))
      · push_neg at hz
        obtain ⟨i, hi⟩ := hz
        exact Or.inl ⟨i, Finset.mem_sdiff.mpr ⟨hi, hw⟩⟩

theorem d_compl (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) : d H Aᶜ = d H A := by
  unfold d
  congr 1
  apply Multiset.filter_congr
  intro e _
  rw [compl_compl, and_comm]

theorem exists_ne2 {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) : ∃ m, m ≠ i ∧ m ≠ j := by
  have h1 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset (Fin n))) (a := i)
  have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ.erase i)) (a := j)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  obtain ⟨m, hm⟩ : ((Finset.univ.erase i).erase j).Nonempty := by
    rw [← Finset.card_pos]; omega
  exact ⟨m, (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1, (Finset.mem_erase.mp hm).1⟩

theorem succAbove_cases {n : ℕ} (m a : Fin (n + 1)) : a = m ∨ ∃ b, m.succAbove b = a := by
  by_cases h : a = m
  · exact Or.inl h
  · exact Or.inr (Fin.exists_succAbove_eq h)

theorem base (H : HyperKCut.Structure.Hypergraph V) {R U : Finset V} {u : Fin 2 → V}
    {A : Fin 2 → Finset V} (h : Good H 2 R U u A) (i j : Fin 2) (hij : i ≠ j) :
    sigma H (Ys A) (Ws A) (Zs A) ≤ d H (A i) + d H (A j) := by
  have hP := good_partition (le_refl 2) h
  have hYeq : (![Ys A 0, Ys A 1] : Fin 2 → Finset V) = Ys A := by
    funext k; fin_cases k <;> rfl
  have hWsub : ∀ k : Fin 2, Ws A ⊆ A k := by
    intro k v hv
    obtain ⟨a, b, hab, ha, hb⟩ := (mem_Ws A v).mp hv
    fin_cases k <;> fin_cases a <;> fin_cases b <;> simp_all
  have hE := proposition_3_1 H (Ys A 0) (Ys A 1) (Ws A) (Zs A) (by rw [hYeq]; exact hP)
  rw [hYeq] at hE
  have e0 : Ys A 0 ∪ Ws A = A 0 := Finset.sdiff_union_of_subset (hWsub 0)
  have e1 : Ys A 1 ∪ Ws A = A 1 := Finset.sdiff_union_of_subset (hWsub 1)
  rw [e0, e1] at hE
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

theorem step (H : HyperKCut.Structure.Hypergraph V) (q : ℕ) (hq : 2 ≤ q)
    (IH : ∀ (R U : Finset V) (u : Fin q → V) (A : Fin q → Finset V), Good H q R U u A →
      ∀ i j, i ≠ j → sigma H (Ys A) (Ws A) (Zs A) ≤ d H (A i) + d H (A j))
    (R U : Finset V) (u : Fin (q + 1) → V) (A : Fin (q + 1) → Finset V)
    (h : Good H (q + 1) R U u A) (i j : Fin (q + 1)) (hij : i ≠ j) :
    sigma H (Ys A) (Ws A) (Zs A) ≤ d H (A i) + d H (A j) := by
  have hP := good_partition (by omega) h
  have hUc := good_Uc h
  have hRo := good_R h
  obtain ⟨hRn, hRU, hUV, hinj, hu, hA, hui, huj⟩ := h
  obtain ⟨m, hmi, hmj⟩ := exists_ne2 (by omega) i j
  obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq (Ne.symm hmi)
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Ne.symm hmj)
  set A' : Fin q → Finset V := fun k => A (m.succAbove k) with hA'
  set u' : Fin q → V := fun k => u (m.succAbove k) with hu'
  set R' : Finset V := insert (u m) R with hR'
  have hsrc : ∀ k, ((Finset.univ.image u') ∪ R').erase (u' k) =
      ((Finset.univ.image u) ∪ R).erase (u (m.succAbove k)) := by
    intro k
    congr 1
    ext v
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, hR',
      Finset.mem_insert, hu']
    constructor
    · rintro (⟨a, rfl⟩ | rfl | hr)
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inl ⟨m, rfl⟩
      · exact Or.inr hr
    · rintro (⟨a, rfl⟩ | hr)
      · rcases succAbove_cases m a with rfl | ⟨b, rfl⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl ⟨b, rfl⟩
      · exact Or.inr (Or.inr hr)
  have hG' : Good H q R' U u' A' := by
    refine ⟨Finset.insert_nonempty _ _, ?_, hUV, hinj.comp Fin.succAbove_right_injective,
      ?_, ?_, fun k => hui _, fun k l hkl => huj _ _ ?_⟩
    · rw [Finset.ssubset_iff_of_subset]
      · refine ⟨u (m.succAbove ⟨0, by omega⟩), (Finset.mem_sdiff.mp (hu _)).1, ?_⟩
        rw [hR', Finset.mem_insert]
        rintro (h | h)
        · exact Fin.succAbove_ne m _ (hinj h)
        · exact (Finset.mem_sdiff.mp (hu _)).2 h
      · exact Finset.insert_subset (Finset.mem_sdiff.mp (hu m)).1 hRU.1
    · intro k
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (hu _)).1, ?_⟩
      rw [hR', Finset.mem_insert]
      rintro (h | h)
      · exact Fin.succAbove_ne m _ (hinj h)
      · exact (Finset.mem_sdiff.mp (hu _)).2 h
    · intro k
      rw [hsrc k]
      exact hA _
    · exact fun e => hkl (Fin.succAbove_right_injective e)
  have hP' := good_partition hq hG'
  have IHij := IH R' U u' A' hG' i' j' (fun e => hij (by rw [← hi', ← hj', e]))
  -- set identities
  have eW : Ws A' ∪ (A m \ Zs A') = Ws A := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, mem_Ws, mem_Zs, hA']
    push_neg
    constructor
    · rintro (⟨a, b, hab, ha, hb⟩ | ⟨hm, k, hk⟩)
      · exact ⟨_, _, fun e => hab (Fin.succAbove_right_injective e), ha, hb⟩
      · exact ⟨m, _, (Fin.succAbove_ne m k).symm, hm, hk⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      rcases succAbove_cases m a with rfl | ⟨a', rfl⟩
      · rcases succAbove_cases a b with rfl | ⟨b', rfl⟩
        · exact absurd rfl hab
        · exact Or.inr ⟨ha, b', hb⟩
      · rcases succAbove_cases m b with rfl | ⟨b', rfl⟩
        · exact Or.inr ⟨hb, a', ha⟩
        · exact Or.inl ⟨a', b', fun e => hab (by rw [e]), ha, hb⟩
  have eZ : Zs A' \ A m = Zs A := by
    ext v
    simp only [Finset.mem_sdiff, mem_Zs, hA']
    constructor
    · rintro ⟨h1, h2⟩ a
      rcases succAbove_cases m a with rfl | ⟨a', rfl⟩
      · exact h2
      · exact h1 a'
    · intro h; exact ⟨fun k => h _, h m⟩
  have eY : ∀ k, Ys A' k \ A m = Ys A (m.succAbove k) := by
    intro k
    ext v
    simp only [Ys, ← eW, Finset.mem_sdiff, Finset.mem_union, mem_Zs, hA']
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, fun h => h.elim h2 (fun h' => h3 h'.1)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun h => h2 (Or.inl h)⟩, fun h => h2 (Or.inr ⟨h, fun h' => h' k h1⟩)⟩
  have eYm : A m ∩ Zs A' = Ys A m := by
    ext v
    simp only [Ys, ← eW, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro (h | h)
      · obtain ⟨a, _, _, ha, _⟩ := (mem_Ws A' v).mp h
        exact (mem_Zs A' v).mp h2 a ha
      · exact h.2 h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra hc
      exact h2 (Or.inr ⟨h1, hc⟩)
  -- apply Lemma 3.1
  have L := lemma_3_1 H q (by omega) (Ys A') (Ws A') (Zs A') hP' (A m)
    (by
      intro k
      refine ⟨u (m.succAbove k), ?_⟩
      rw [eY]
      exact Finset.mem_sdiff.mpr ⟨hui _, fun hw => by
        obtain ⟨a, b, hab, ha, hb⟩ := (mem_Ws A _).mp hw
        by_cases h1 : m.succAbove k = a
        · subst h1; exact huj _ b hab hb
        · exact huj _ a h1 ha⟩)
    (by
      refine ⟨u m, Finset.mem_inter.mpr ⟨hui m, (mem_Zs A' _).mpr fun k => ?_⟩⟩
      exact huj m _ (Fin.succAbove_ne m k).symm)
    (by
      obtain ⟨r, hr⟩ := hRn
      exact ⟨r, by rw [eZ]; exact (mem_Zs A r).mpr fun a => hRo a r hr⟩)
    (by
      obtain ⟨v, -, hv⟩ := Finset.exists_of_ssubset hUV
      exact ⟨v, by rw [eW]; exact (mem_Ws A v).mpr ⟨m, _, (Fin.succAbove_ne m ⟨0, by omega⟩).symm,
        hUc _ v hv, hUc _ v hv⟩⟩)
  have Lp : IsPartitionYWZ
      (Fin.snoc (α := fun _ => Finset V) (fun k => Ys A' k \ A m) (A m ∩ Zs A'))
      (Ws A' ∪ (A m \ Zs A')) (Zs A' \ A m) := L.1
  have Lσ : sigma H
      (Fin.snoc (α := fun _ => Finset V) (fun k => Ys A' k \ A m) (A m ∩ Zs A'))
      (Ws A' ∪ (A m \ Zs A')) (Zs A' \ A m) + d H (Ws A' ∩ A m) ≤
      sigma H (Ys A') (Ws A') (Zs A') + d H (A m) := L.2
  clear L
  rw [eW, eZ] at Lp Lσ
  have hσ : sigma H (Fin.snoc (α := fun _ => Finset V) (fun k => Ys A' k \ A m) (A m ∩ Zs A'))
      (Ws A) (Zs A) = sigma H (Ys A) (Ws A) (Zs A) := by
    rw [sigma_eq _ _ _ _ Lp, sigma_eq _ _ _ _ hP]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun e _ => ?_)
    have hn : numYMet e (Fin.snoc (α := fun _ => Finset V) (fun k => Ys A' k \ A m)
        (A m ∩ Zs A')) = numYMet e (Ys A) := by
      rw [HKL31Aux.numYMet_sum, HKL31Aux.numYMet_sum, Fin.sum_univ_castSucc,
        Fin.sum_univ_succAbove _ m]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, eY, eYm]
      ring
    rw [hn]
  rw [hσ] at Lσ
  have hmin : d H (A m) ≤ d H (Ws A' ∩ A m) := by
    have := (hA m).2 (Ws A' ∩ A m)ᶜ ⟨?_, ?_⟩
    · rwa [d_compl, d_compl] at this
    · exact le_trans (hA m).1.1 (Finset.compl_subset_compl.mpr Finset.inter_subset_right)
    · rw [Finset.disjoint_left]
      intro v hv hvU
      apply Finset.mem_compl.mp hv
      have hvU' : v ∉ U := Finset.mem_compl.mp hvU
      refine Finset.mem_inter.mpr ⟨(mem_Ws A' v).mpr ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_,
        hUc _ v hvU', hUc _ v hvU'⟩, hUc _ v hvU'⟩
      simp [Fin.ext_iff]
  have e1 : A' i' = A i := by simp [hA', hi']
  have e2 : A' j' = A j := by simp [hA', hj']
  rw [e1, e2] at IHij
  omega

theorem main (H : HyperKCut.Structure.Hypergraph V) (p : ℕ) (hp : 2 ≤ p) :
    ∀ (R U : Finset V) (u : Fin p → V) (A : Fin p → Finset V), Good H p R U u A →
      ∀ i j, i ≠ j → sigma H (Ys A) (Ws A) (Zs A) ≤ d H (A i) + d H (A j) := by
  induction p, hp using Nat.le_induction with
  | base => intro R U u A h i j hij; exact base H h i j hij
  | succ q hq IH => exact step H q hq IH

end HKL32Aux

open HKSigAux HKYWZAux HKL32Aux in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : HyperKCut.Structure.Hypergraph V)
    (p : ℕ) (hp : 2 ≤ p)
    (R U : Finset V) (hR : R.Nonempty) (hRU : R ⊂ U)
    (hUV : U ⊂ (Finset.univ : Finset V))
    (u : Fin p → V) (huinj : Function.Injective u)
    (hu : ∀ i, u i ∈ U \ R)
    (A : Fin p → Finset V)
    (hA : ∀ i, IsMinTerminalCut H
      (((Finset.univ.image u) ∪ R).erase (u i)) Uᶜ (A i)ᶜ)
    (hui : ∀ i, u i ∈ A i)
    (huj : ∀ i j, i ≠ j → u i ∉ A j) :
    let Z : Finset V := Finset.univ.filter (fun v => ∀ i, v ∉ A i)
    let W : Finset V := Finset.univ.filter
      (fun v => ∃ i j : Fin p, i ≠ j ∧ v ∈ A i ∧ v ∈ A j)
    let Y : Fin p → Finset V := fun i => A i \ W
    IsPartitionYWZ Y W Z ∧
      ∀ i j : Fin p, i ≠ j → sigma H Y W Z ≤ d H (A i) + d H (A j) := by
  intro Z W Y
  have hG : Good H p R U u A := ⟨hR, hRU, hUV, huinj, hu, hA, hui, huj⟩
  exact ⟨good_partition hp hG, main H p hp R U u A hG⟩
