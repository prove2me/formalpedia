-- Prove2me | solution 1 for HyperKCut.Structure.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:35:43.13299+00:00
-- url     : https://prove2.me/submissions/192f533f-9dd6-46e8-b13b-7fd717cba06c

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

namespace HKL31Aux
open HKSigAux

theorem sigB_min (n : ℕ) (w z : Bool) : sigB n w z = sigB (min n 2) w z := by
  rcases n with _ | _ | n
  · rfl
  · rfl
  · have : min (n + 2) 2 = 2 := by omega
    rw [this]
    cases w <;> cases z <;> simp [sigB] <;> omega

theorem arithF : ∀ a b c : Fin 3, ∀ wq wo zq zo : Bool, a.val ≤ c.val → b.val ≤ c.val →
    c.val ≤ a.val + b.val →
    sigB (min (a.val + zq.toNat) 2) (wq || wo || decide (1 ≤ b.val)) zo +
      (if wq = true ∧ (1 ≤ c.val ∨ wo = true ∨ zq = true ∨ zo = true) then 1 else 0) ≤
    sigB c.val (wq || wo) (zq || zo) +
      (if (1 ≤ b.val ∨ wq = true ∨ zq = true) ∧ (1 ≤ a.val ∨ wo = true ∨ zo = true) then 1 else 0) := by
  decide

theorem arith (xo xq nX : ℕ) (wq wo zq zo : Bool)
    (h1 : xo ≤ nX) (h2 : xq ≤ nX) (h3 : nX ≤ xo + xq) :
    sigB (xo + zq.toNat) (wq || wo || decide (1 ≤ xq)) zo +
      (if wq = true ∧ (1 ≤ nX ∨ wo = true ∨ zq = true ∨ zo = true) then 1 else 0) ≤
    sigB nX (wq || wo) (zq || zo) +
      (if (1 ≤ xq ∨ wq = true ∨ zq = true) ∧ (1 ≤ xo ∨ wo = true ∨ zo = true) then 1 else 0) := by
  have key := arithF ⟨min xo 2, by omega⟩ ⟨min xq 2, by omega⟩ ⟨min nX 2, by omega⟩ wq wo zq zo
    (by simp only; omega) (by simp only; omega) (by simp only; omega)
  simp only at key
  have e1 : min (min xo 2 + zq.toNat) 2 = min (xo + zq.toNat) 2 := by omega
  have e2 : decide (1 ≤ min xq 2) = decide (1 ≤ xq) := by
    apply decide_eq_decide.mpr; omega
  have e3 : (1 ≤ min nX 2) ↔ 1 ≤ nX := by omega
  have e4 : (1 ≤ min xq 2) ↔ 1 ≤ xq := by omega
  have e5 : (1 ≤ min xo 2) ↔ 1 ≤ xo := by omega
  rw [e1, e2, ← sigB_min, ← sigB_min] at key
  simp only [e3, e4, e5] at key
  exact key

end HKL31Aux

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

open HKSigAux HKYWZAux HKL31Aux in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : HyperKCut.Structure.Hypergraph V)
    (p : ℕ) (hp : 1 ≤ p)
    (X : Fin p → Finset V) (W₀ Z₀ : Finset V) (hX : IsPartitionYWZ X W₀ Z₀)
    (Q : Finset V)
    (hY : ∀ i, (X i \ Q).Nonempty) (hYp : (Q ∩ Z₀).Nonempty)
    (hZ : (Z₀ \ Q).Nonempty) (hW : (W₀ ∪ (Q \ Z₀)).Nonempty) :
    let Y : Fin (p + 1) → Finset V := Fin.snoc (α := fun _ => Finset V) (fun i => X i \ Q) (Q ∩ Z₀)
    let W : Finset V := W₀ ∪ (Q \ Z₀)
    let Z : Finset V := Z₀ \ Q
    IsPartitionYWZ Y W Z ∧
      sigma H Y W Z + d H (W₀ ∩ Q) ≤ sigma H X W₀ Z₀ + d H Q := by
  intro Y W Z
  obtain ⟨_, _, _, hXX, hXW, hXZ, hWZ, hcov⟩ := ywz_facts X W₀ Z₀ hX
  have eYc : ∀ i, Y (Fin.castSucc i) = X i \ Q := fun i => by simp [Y]
  have eYl : Y (Fin.last p) = Q ∩ Z₀ := by simp [Y]
  have hPart : IsPartitionYWZ Y W Z := by
    apply ywz_mk
    · intro i
      induction i using Fin.lastCases with
      | last => rw [eYl]; exact hYp
      | cast i => rw [eYc]; exact hY i
    · exact hW
    · exact hZ
    · intro i j hij
      rw [Finset.disjoint_left]
      intro v hvi hvj
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact hij rfl
        | cast j =>
          rw [eYl] at hvi; rw [eYc] at hvj
          exact Finset.disjoint_left.mp (hXZ j) (Finset.mem_sdiff.mp hvj).1
            (Finset.mem_inter.mp hvi).2
      | cast i =>
        rw [eYc] at hvi
        induction j using Fin.lastCases with
        | last =>
          rw [eYl] at hvj
          exact Finset.disjoint_left.mp (hXZ i) (Finset.mem_sdiff.mp hvi).1
            (Finset.mem_inter.mp hvj).2
        | cast j =>
          rw [eYc] at hvj
          exact Finset.disjoint_left.mp (hXX i j (fun h => hij (by rw [h])))
            (Finset.mem_sdiff.mp hvi).1 (Finset.mem_sdiff.mp hvj).1
    · intro i
      rw [Finset.disjoint_left]
      intro v hvi hvW
      induction i using Fin.lastCases with
      | last =>
        rw [eYl] at hvi
        rcases Finset.mem_union.mp hvW with h | h
        · exact Finset.disjoint_left.mp hWZ h (Finset.mem_inter.mp hvi).2
        · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hvi).2
      | cast i =>
        rw [eYc] at hvi
        rcases Finset.mem_union.mp hvW with h | h
        · exact Finset.disjoint_left.mp (hXW i) (Finset.mem_sdiff.mp hvi).1 h
        · exact (Finset.mem_sdiff.mp hvi).2 (Finset.mem_sdiff.mp h).1
    · intro i
      rw [Finset.disjoint_left]
      intro v hvi hvZ
      induction i using Fin.lastCases with
      | last =>
        rw [eYl] at hvi
        exact (Finset.mem_sdiff.mp hvZ).2 (Finset.mem_inter.mp hvi).1
      | cast i =>
        rw [eYc] at hvi
        exact Finset.disjoint_left.mp (hXZ i) (Finset.mem_sdiff.mp hvi).1
          (Finset.mem_sdiff.mp hvZ).1
    · rw [Finset.disjoint_left]
      intro v hvW hvZ
      rcases Finset.mem_union.mp hvW with h | h
      · exact Finset.disjoint_left.mp hWZ h (Finset.mem_sdiff.mp hvZ).1
      · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mp hvZ).1
    · intro v
      rcases hcov v with ⟨i, hi⟩ | h | h
      · by_cases hq : v ∈ Q
        · right; left
          refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hq, fun hz => ?_⟩)
          exact Finset.disjoint_left.mp (hXZ i) hi hz
        · left; exact ⟨Fin.castSucc i, by rw [eYc]; exact Finset.mem_sdiff.mpr ⟨hi, hq⟩⟩
      · right; left; exact Finset.mem_union_left _ h
      · by_cases hq : v ∈ Q
        · left; exact ⟨Fin.last p, by rw [eYl]; exact Finset.mem_inter.mpr ⟨hq, h⟩⟩
        · right; right; exact Finset.mem_sdiff.mpr ⟨h, hq⟩
  refine ⟨hPart, ?_⟩
  rw [sigma_eq H Y W Z hPart, sigma_eq H X W₀ Z₀ hX, d_eq_sum, d_eq_sum,
    ← Multiset.sum_map_add, ← Multiset.sum_map_add]
  apply Multiset.sum_map_le_sum_map
  intro e _
  -- the per-edge quantities
  set xo := numYMet e (fun i => X i \ Q) with hxo
  set xq := numYMet e (fun i => X i ∩ Q) with hxq
  set nX := numYMet e X with hnX
  set wq := decide (Meets e (W₀ ∩ Q)) with hwq
  set wo := decide (Meets e (W₀ \ Q)) with hwo
  set zq := decide (Meets e (Q ∩ Z₀)) with hzq
  set zo := decide (Meets e (Z₀ \ Q)) with hzo
  have h1 : xo ≤ nX := by
    rw [hxo, hnX]; unfold numYMet
    apply Finset.card_le_card
    intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, meets_iff]
    rintro ⟨v, hv, hv'⟩; exact ⟨v, hv, (Finset.mem_sdiff.mp hv').1⟩
  have h2 : xq ≤ nX := by
    rw [hxq, hnX]; unfold numYMet
    apply Finset.card_le_card
    intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, meets_iff]
    rintro ⟨v, hv, hv'⟩; exact ⟨v, hv, (Finset.mem_inter.mp hv').1⟩
  have h3 : nX ≤ xo + xq := by
    rw [hxo, hxq, hnX]; unfold numYMet
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, meets_iff,
      Finset.mem_union]
    rintro ⟨v, hv, hv'⟩
    by_cases hq : v ∈ Q
    · right; exact ⟨v, hv, Finset.mem_inter.mpr ⟨hv', hq⟩⟩
    · left; exact ⟨v, hv, Finset.mem_sdiff.mpr ⟨hv', hq⟩⟩
  have key := arith xo xq nX wq wo zq zo h1 h2 h3
  -- rewrite the left-hand side
  have eY : numYMet e Y = xo + zq.toNat := by
    rw [numYMet_sum, Fin.sum_univ_castSucc, hxo, numYMet_sum]
    simp only [eYc, eYl, hzq]
    by_cases h : Meets e (Q ∩ Z₀) <;> simp [h]
  have eW : decide (Meets e W) = (wq || wo || decide (1 ≤ xq)) := by
    have hq1 : (1 ≤ xq) ↔ ∃ i, Meets e (X i ∩ Q) := one_le_numYMet _ _
    rw [hwq, hwo]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [hq1]
    simp only [meets_iff, W, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨v, hv, h | ⟨hq, hz⟩⟩
      · by_cases hq : v ∈ Q
        · exact Or.inl (Or.inl ⟨v, hv, h, hq⟩)
        · exact Or.inl (Or.inr ⟨v, hv, h, hq⟩)
      · rcases hcov v with ⟨i, hi⟩ | h | h
        · exact Or.inr ⟨i, v, hv, hi, hq⟩
        · exact Or.inl (Or.inl ⟨v, hv, h, hq⟩)
        · exact absurd h hz
    · rintro ((⟨v, hv, h, _⟩ | ⟨v, hv, h, _⟩) | ⟨i, v, hv, hi, hq⟩)
      · exact ⟨v, hv, Or.inl h⟩
      · exact ⟨v, hv, Or.inl h⟩
      · exact ⟨v, hv, Or.inr ⟨hq, fun hz => Finset.disjoint_left.mp (hXZ i) hi hz⟩⟩
  have eW0 : decide (Meets e W₀) = (wq || wo) := by
    rw [hwq, hwo]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, meets_iff, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨v, hv, h⟩
      by_cases hq : v ∈ Q
      · exact Or.inl ⟨v, hv, h, hq⟩
      · exact Or.inr ⟨v, hv, h, hq⟩
    · rintro (⟨v, hv, h, _⟩ | ⟨v, hv, h, _⟩) <;> exact ⟨v, hv, h⟩
  have eZ0 : decide (Meets e Z₀) = (zq || zo) := by
    rw [hzq, hzo]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, meets_iff, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨v, hv, h⟩
      by_cases hq : v ∈ Q
      · exact Or.inl ⟨v, hv, hq, h⟩
      · exact Or.inr ⟨v, hv, h, hq⟩
    · rintro (⟨v, hv, _, h⟩ | ⟨v, hv, h, _⟩) <;> exact ⟨v, hv, h⟩
  have eL : (Meets e (W₀ ∩ Q) ∧ Meets e (W₀ ∩ Q)ᶜ) ↔
      (wq = true ∧ (1 ≤ nX ∨ wo = true ∨ zq = true ∨ zo = true)) := by
    rw [hwq, hwo, hzq, hzo, hnX, one_le_numYMet]
    simp only [decide_eq_true_eq]
    apply and_congr Iff.rfl
    simp only [meets_iff, Finset.mem_compl, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨v, hv, hn⟩
      rcases hcov v with ⟨i, hi⟩ | h | h
      · exact Or.inl ⟨i, v, hv, hi⟩
      · exact Or.inr (Or.inl ⟨v, hv, h, fun hq => hn ⟨h, hq⟩⟩)
      · by_cases hq : v ∈ Q
        · exact Or.inr (Or.inr (Or.inl ⟨v, hv, hq, h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨v, hv, h, hq⟩))
    · rintro (⟨i, v, hv, hi⟩ | ⟨v, hv, _, hq⟩ | ⟨v, hv, _, h⟩ | ⟨v, hv, h, _⟩)
      · exact ⟨v, hv, fun h => Finset.disjoint_left.mp (hXW i) hi h.1⟩
      · exact ⟨v, hv, fun h => hq h.2⟩
      · exact ⟨v, hv, fun h' => Finset.disjoint_left.mp hWZ h'.1 h⟩
      · exact ⟨v, hv, fun h' => Finset.disjoint_left.mp hWZ h'.1 h⟩
  have eR : (Meets e Q ∧ Meets e Qᶜ) ↔
      ((1 ≤ xq ∨ wq = true ∨ zq = true) ∧ (1 ≤ xo ∨ wo = true ∨ zo = true)) := by
    rw [hwq, hwo, hzq, hzo, hxq, hxo, one_le_numYMet, one_le_numYMet]
    simp only [decide_eq_true_eq]
    simp only [meets_iff, Finset.mem_compl, Finset.mem_inter, Finset.mem_sdiff]
    apply and_congr
    · constructor
      · rintro ⟨v, hv, hq⟩
        rcases hcov v with ⟨i, hi⟩ | h | h
        · exact Or.inl ⟨i, v, hv, hi, hq⟩
        · exact Or.inr (Or.inl ⟨v, hv, h, hq⟩)
        · exact Or.inr (Or.inr ⟨v, hv, hq, h⟩)
      · rintro (⟨i, v, hv, _, hq⟩ | ⟨v, hv, _, hq⟩ | ⟨v, hv, hq, _⟩) <;> exact ⟨v, hv, hq⟩
    · constructor
      · rintro ⟨v, hv, hq⟩
        rcases hcov v with ⟨i, hi⟩ | h | h
        · exact Or.inl ⟨i, v, hv, hi, hq⟩
        · exact Or.inr (Or.inl ⟨v, hv, h, hq⟩)
        · exact Or.inr (Or.inr ⟨v, hv, h, hq⟩)
      · rintro (⟨i, v, hv, _, hq⟩ | ⟨v, hv, _, hq⟩ | ⟨v, hv, _, hq⟩) <;> exact ⟨v, hv, hq⟩
  have eZ : decide (Meets e Z) = zo := rfl
  rw [eY, eW, eW0, eZ0, if_congr eL rfl rfl, if_congr eR rfl rfl]
  exact key
