-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.natCard_edge_eq_x0MqAdjV4
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/326ff20c-95c7-53f5-a3b2-2c762cd86236

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_natCard_edge_eq_x0MqAdjV4

set_option autoImplicit false

open ModularCurve

namespace S17PL3

p2m_open "ModularCurve.DRResolvedModelPackage"

variable {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ)

def P (v w : X0MqComponents width) (e : Σ n : node, Fin (width n)) : Prop :=
  (v = chainPos width e.1 e.2 ∧ w = chainPos width e.1 (e.2 + 1)) ∨
    (w = chainPos width e.1 e.2 ∧ v = chainPos width e.1 (e.2 + 1))

theorem P_comm (v w : X0MqComponents width) (e : Σ n : node, Fin (width n)) : P width v w e ↔ P width w v e := by
  unfold P; tauto

theorem chainPos_zero (n : node) : chainPos width n 0 = Sum.inl 0 := by
  simp [chainPos]

theorem chainPos_of_pos_of_lt (n : node) {d : ℕ} (h0 : d ≠ 0) (h : d < width n) :
    chainPos width n d = Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩ := by
  simp [chainPos, h0, h]

theorem chainPos_of_le (n : node) {d : ℕ} (h0 : d ≠ 0) (h : width n ≤ d) :
    chainPos width n d = Sum.inl 1 := by
  simp [chainPos, h0, Nat.not_lt.mpr h]

theorem natCard_eq_sum (v w : X0MqComponents width) [DecidablePred (P width v w)] :
    Nat.card {e : Σ n : node, Fin (width n) // P width v w e}
      = ∑ n, (Finset.univ.filter fun d : Fin (width n) => P width v w ⟨n, d⟩).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, ← Finset.univ_sigma_univ,
    Finset.sum_sigma]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.card_filter]

def enc : X0MqComponents width → Fin 2 ⊕ (node × ℕ)
  | .inl i => .inl i
  | .inr x => .inr (x.1, x.2.val)

theorem enc_injective : Function.Injective (enc width) := by
  rintro (i | ⟨n, k⟩) (j | ⟨n', k'⟩) h
  · simpa [enc] using h
  · simp [enc] at h
  · simp [enc] at h
  · simp only [enc, Sum.inr.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hk⟩ := h
    have : k = k' := Fin.ext hk
    subst this
    rfl

theorem enc_eq_iff {a b : X0MqComponents width} : enc width a = enc width b ↔ a = b :=
  (enc_injective width).eq_iff

theorem enc_chainPos_fst (n : node) (d : Fin (width n)) :
    enc width (chainPos width n d) = if (d : ℕ) = 0 then Sum.inl 0 else Sum.inr (n, (d : ℕ) - 1) := by
  by_cases h0 : (d : ℕ) = 0
  · rw [if_pos h0, h0, chainPos_zero]; rfl
  · rw [if_neg h0, chainPos_of_pos_of_lt width n h0 d.isLt]; rfl

theorem enc_chainPos_snd (n : node) (d : Fin (width n)) :
    enc width (chainPos width n ((d : ℕ) + 1))
      = if (d : ℕ) + 1 < width n then Sum.inr (n, (d : ℕ)) else Sum.inl 1 := by
  by_cases h : (d : ℕ) + 1 < width n
  · rw [if_pos h, chainPos_of_pos_of_lt width n (Nat.succ_ne_zero _) h]
    simp [enc]
  · rw [if_neg h, chainPos_of_le width n (Nat.succ_ne_zero _) (Nat.not_lt.mp h)]; rfl

theorem P_iff (v w : X0MqComponents width) (n : node) (d : Fin (width n)) :
    P width v w ⟨n, d⟩ ↔
      (enc width v = (if (d : ℕ) = 0 then Sum.inl 0 else Sum.inr (n, (d : ℕ) - 1)) ∧
        enc width w = (if (d : ℕ) + 1 < width n then Sum.inr (n, (d : ℕ)) else Sum.inl 1)) ∨
      (enc width w = (if (d : ℕ) = 0 then Sum.inl 0 else Sum.inr (n, (d : ℕ) - 1)) ∧
        enc width v = (if (d : ℕ) + 1 < width n then Sum.inr (n, (d : ℕ)) else Sum.inl 1)) := by
  unfold P
  rw [← enc_chainPos_fst, ← enc_chainPos_snd, enc_eq_iff, enc_eq_iff, enc_eq_iff, enc_eq_iff]

theorem card_filter_eq_ite (n : node) (c : Prop) [Decidable c] (q : Fin (width n) → Prop) [DecidablePred q]
    (d₀ : ℕ) (h : ∀ d : Fin (width n), q d ↔ (c ∧ (d : ℕ) = d₀)) (hd₀ : c → d₀ < width n) :
    (Finset.univ.filter q).card = if c then 1 else 0 := by
  split_ifs with hc
  · rw [Finset.card_eq_one]
    refine ⟨⟨d₀, hd₀ hc⟩, Finset.ext fun d => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, h, hc, Fin.ext_iff]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d _ hq
    exact hc ((h d).mp hq).1

theorem inner_inl_inl (i j : Fin 2) (hij : i ≠ j) (n : node) [DecidablePred (P width (Sum.inl i) (Sum.inl j))] :
    (Finset.univ.filter fun d : Fin (width n) => P width (Sum.inl i) (Sum.inl j) ⟨n, d⟩).card
      = if width n = 1 then 1 else 0 := by
  apply card_filter_eq_ite width n (width n = 1) _ 0
  · intro d
    rw [P_iff]
    have hd := d.isLt
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp only [enc]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · split_ifs at h1 h2 with ha hb <;> simp at h1 h2
          omega
        · split_ifs at h1 h2 with ha hb <;> simp at h1 h2
      · rintro ⟨hw, hd0⟩
        left
        rw [if_pos hd0, if_neg (by omega)]
        exact ⟨rfl, rfl⟩
    · simp only [enc]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · split_ifs at h1 h2 with ha hb <;> simp at h1 h2
        · split_ifs at h1 h2 with ha hb <;> simp at h1 h2
          omega
      · rintro ⟨hw, hd0⟩
        right
        rw [if_pos hd0, if_neg (by omega)]
        exact ⟨rfl, rfl⟩
    · exact absurd rfl hij
  · intro h; omega

theorem inner_inl0_inr (x : Σ m : node, Fin (width m - 1)) (n : node)
    [DecidablePred (P width (Sum.inl 0) (Sum.inr x))] :
    (Finset.univ.filter fun d : Fin (width n) => P width (Sum.inl 0) (Sum.inr x) ⟨n, d⟩).card
      = if (n = x.1 ∧ x.2.val = 0) then 1 else 0 := by
  obtain ⟨m, k⟩ := x
  have hk := k.isLt
  apply card_filter_eq_ite width n (n = m ∧ k.val = 0) _ 0
  · intro d
    rw [P_iff]
    have hd := d.isLt
    simp only [enc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · split_ifs at h1 h2 with ha hb <;> simp at h1 h2
        obtain ⟨rfl, h2⟩ := h2
        exact ⟨⟨rfl, by omega⟩, ha⟩
      · split_ifs at h1 h2 with ha hb <;> simp at h1 h2
    · rintro ⟨⟨rfl, hk0⟩, hd0⟩
      left
      rw [if_pos hd0, if_pos (by omega)]
      refine ⟨rfl, ?_⟩
      simp [hd0, hk0]
  · rintro ⟨rfl, -⟩; omega

theorem inner_inl1_inr (x : Σ m : node, Fin (width m - 1)) (n : node)
    [DecidablePred (P width (Sum.inl 1) (Sum.inr x))] :
    (Finset.univ.filter fun d : Fin (width n) => P width (Sum.inl 1) (Sum.inr x) ⟨n, d⟩).card
      = if (n = x.1 ∧ x.2.val = width x.1 - 2) then 1 else 0 := by
  obtain ⟨m, k⟩ := x
  have hk := k.isLt
  apply card_filter_eq_ite width n (n = m ∧ k.val = width m - 2) _ (width n - 1)
  · intro d
    rw [P_iff]
    have hd := d.isLt
    simp only [enc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · split_ifs at h1 h2 with ha hb <;> simp at h1 h2
      · split_ifs at h1 h2 with ha hb <;> simp at h1 h2
        obtain ⟨rfl, h1⟩ := h1
        exact ⟨⟨rfl, by omega⟩, by omega⟩
    · rintro ⟨⟨rfl, hk0⟩, hd0⟩
      right
      rw [if_neg (by omega), if_neg (by omega)]
      refine ⟨?_, rfl⟩
      simp only [Sum.inr.injEq, Prod.mk.injEq, true_and]
      omega
  · rintro ⟨rfl, -⟩; omega

theorem inner_inr_inr (x y : Σ m : node, Fin (width m - 1)) (n : node)
    [DecidablePred (P width (Sum.inr x) (Sum.inr y))] :
    (Finset.univ.filter fun d : Fin (width n) => P width (Sum.inr x) (Sum.inr y) ⟨n, d⟩).card
      = if (n = x.1 ∧ x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) then 1 else 0 := by
  obtain ⟨m, k⟩ := x
  obtain ⟨m', k'⟩ := y
  have hk := k.isLt
  have hk' := k'.isLt
  apply card_filter_eq_ite width n (n = m ∧ m = m' ∧ (k.val + 1 = k'.val ∨ k'.val + 1 = k.val)) _
    (min k.val k'.val + 1)
  · intro d
    rw [P_iff]
    have hd := d.isLt
    simp only [enc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · split_ifs at h1 h2 with ha hb <;> simp at h1 h2
        obtain ⟨rfl, h1⟩ := h1
        obtain ⟨rfl, h2⟩ := h2
        exact ⟨⟨rfl, rfl, by omega⟩, by omega⟩
      · split_ifs at h1 h2 with ha hb <;> simp at h1 h2
        obtain ⟨rfl, h1⟩ := h1
        obtain ⟨rfl, h2⟩ := h2
        exact ⟨⟨rfl, rfl, by omega⟩, by omega⟩
    · rintro ⟨⟨rfl, rfl, hkk⟩, hd0⟩
      rcases hkk with hkk | hkk
      · left
        rw [if_neg (by omega), if_pos (by omega)]
        constructor
        · simp only [Sum.inr.injEq, Prod.mk.injEq, true_and]; omega
        · simp only [Sum.inr.injEq, Prod.mk.injEq, true_and]; omega
      · right
        rw [if_neg (by omega), if_pos (by omega)]
        constructor
        · simp only [Sum.inr.injEq, Prod.mk.injEq, true_and]; omega
        · simp only [Sum.inr.injEq, Prod.mk.injEq, true_and]; omega
  · rintro ⟨rfl, rfl, hkk⟩; omega

theorem natCard_comm (v w : X0MqComponents width) :
    Nat.card {e : Σ n : node, Fin (width n) // P width v w e} = Nat.card {e : Σ n : node, Fin (width n) // P width w v e} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun e => P_comm width v w e

theorem sum_ite_and_eq {c : node → Prop} [DecidablePred c] (m : node) :
    (∑ n, if (n = m ∧ c n) then 1 else 0) = if c m then 1 else 0 := by
  rw [Finset.sum_eq_single m]
  · simp
  · intro n _ hn
    rw [if_neg (fun h => hn h.1)]
  · intro h; exact absurd (Finset.mem_univ m) h

theorem natCard_edge_eq (v w : X0MqComponents width) (hvw : v ≠ w) :
    Nat.card {e : Σ n : node, Fin (width n) // P width v w e} = x0MqAdj width v w := by
  classical
  rcases v with i | x <;> rcases w with j | y
  ·
    have hij : i ≠ j := fun h => hvw (by rw [h])
    have h := Finset.sum_congr rfl (fun n (_ : n ∈ (Finset.univ : Finset node)) =>
      (by convert inner_inl_inl width i j hij n :
        (Finset.univ.filter fun d : Fin (width n) => P width (Sum.inl i) (Sum.inl j) ⟨n, d⟩).card
          = if width n = 1 then 1 else 0))
    rw [natCard_eq_sum, h, x0MqAdj, if_pos hij, Finset.card_filter]
  ·
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · have h := Finset.sum_congr rfl (fun n (_ : n ∈ (Finset.univ : Finset node)) =>
        (by convert inner_inl0_inr width y n :
          (Finset.univ.filter fun d : Fin (width n) => P width (Sum.inl 0) (Sum.inr y) ⟨n, d⟩).card
            = if (n = y.1 ∧ y.2.val = 0) then 1 else 0))
      rw [natCard_eq_sum, h, sum_ite_and_eq]
      simp [x0MqAdj]
    · have h := Finset.sum_congr rfl (fun n (_ : n ∈ (Finset.univ : Finset node)) =>
        (by convert inner_inl1_inr width y n :
          (Finset.univ.filter fun d : Fin (width n) => P width (Sum.inl 1) (Sum.inr y) ⟨n, d⟩).card
            = if (n = y.1 ∧ y.2.val = width y.1 - 2) then 1 else 0))
      rw [natCard_eq_sum, h, sum_ite_and_eq]
      simp [x0MqAdj]
  ·
    rw [natCard_comm, x0MqAdj_symm]
    obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    · have h := Finset.sum_congr rfl (fun n (_ : n ∈ (Finset.univ : Finset node)) =>
        (by convert inner_inl0_inr width x n :
          (Finset.univ.filter fun d : Fin (width n) => P width (Sum.inl 0) (Sum.inr x) ⟨n, d⟩).card
            = if (n = x.1 ∧ x.2.val = 0) then 1 else 0))
      rw [natCard_eq_sum, h, sum_ite_and_eq]
      simp [x0MqAdj]
    · have h := Finset.sum_congr rfl (fun n (_ : n ∈ (Finset.univ : Finset node)) =>
        (by convert inner_inl1_inr width x n :
          (Finset.univ.filter fun d : Fin (width n) => P width (Sum.inl 1) (Sum.inr x) ⟨n, d⟩).card
            = if (n = x.1 ∧ x.2.val = width x.1 - 2) then 1 else 0))
      rw [natCard_eq_sum, h, sum_ite_and_eq]
      simp [x0MqAdj]
  ·
    have h := Finset.sum_congr rfl (fun n (_ : n ∈ (Finset.univ : Finset node)) =>
      (by convert inner_inr_inr width x y n :
        (Finset.univ.filter fun d : Fin (width n) => P width (Sum.inr x) (Sum.inr y) ⟨n, d⟩).card
          = if (n = x.1 ∧ x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) then 1 else 0))
    rw [natCard_eq_sum, h, sum_ite_and_eq]
    simp [x0MqAdj]

end S17PL3

set_option maxHeartbeats 1600000 in
theorem solution
    {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ)
    (v w : X0MqComponents width) (hvw : v ≠ w) :
    Nat.card {e : Σ n : node, Fin (width n) //
        (v = DRResolvedModelPackage.chainPos width e.1 e.2 ∧ w = DRResolvedModelPackage.chainPos width e.1 (e.2 + 1)) ∨
          (w = DRResolvedModelPackage.chainPos width e.1 e.2 ∧ v = DRResolvedModelPackage.chainPos width e.1 (e.2 + 1))} =
      x0MqAdj width v w :=
  S17PL3.natCard_edge_eq width v w hvw

end S_ModularCurve_DRResolvedModelPackage_natCard_edge_eq_x0MqAdjV4
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_natCard_edge_eq_x0MqAdjV4 (solution)
