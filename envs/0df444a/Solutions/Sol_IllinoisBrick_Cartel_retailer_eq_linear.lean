-- Prove2me | solution 1 for IllinoisBrick.Cartel.retailer_eq_linear
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:08:48.486142+00:00
-- url     : https://prove2.me/submissions/7be084d7-7729-48f3-900f-9dc437e2b89e

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model

namespace IllinoisBrick.Cartel

lemma ilb_up_foc {B D : ℝ} (hB : 0 ≤ B) (h : ∀ t : ℝ, 0 < t → t * D - B * t ^ 2 ≤ 0) :
    D ≤ 0 := by
  by_contra hD
  push Not at hD
  have hpos : 0 < 2 * B + 1 := by linarith
  have ht0 : 0 < D / (2 * B + 1) := div_pos hD hpos
  have htD : D / (2 * B + 1) * (2 * B + 1) = D := by field_simp
  have h1 := h (D / (2 * B + 1)) ht0
  set t := D / (2 * B + 1)
  nlinarith [mul_pos ht0 ht0]

lemma ilb_down_foc {B D ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (h : ∀ t : ℝ, -ε < t → t < 0 → t * D - B * t ^ 2 ≤ 0) : 0 ≤ D := by
  by_contra hD
  push Not at hD
  have hpos : 0 < 2 * B + 1 := by linarith
  by_cases hc : -ε < D / (2 * B + 1)
  · have ht0 : D / (2 * B + 1) < 0 := div_neg_of_neg_of_pos hD hpos
    have htD : D / (2 * B + 1) * (2 * B + 1) = D := by field_simp
    have h1 := h _ hc ht0
    set t := D / (2 * B + 1)
    nlinarith [mul_pos (neg_pos.mpr ht0) (neg_pos.mpr ht0)]
  · push Not at hc
    have hD' : D ≤ -ε * (2 * B + 1) := by rwa [div_le_iff₀ hpos] at hc
    have h1 := h (-ε / 2) (by linarith) (by linarith)
    nlinarith [mul_pos hε hε, mul_nonneg hB (mul_pos hε hε).le]

/-- First-order conditions for a concave quadratic payoff `x (K - b x)` maximised at `q`. -/
lemma ilb_quad_up {b K q : ℝ} (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → (q + t) * (K - b * (q + t)) ≤ q * (K - b * q)) :
    K - 2 * b * q ≤ 0 := by
  apply ilb_up_foc hb
  intro t ht
  have := h t ht
  nlinarith

lemma ilb_quad_down {b K q ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (h : ∀ t : ℝ, -ε < t → t < 0 → (q + t) * (K - b * (q + t)) ≤ q * (K - b * q)) :
    0 ≤ K - 2 * b * q := by
  apply ilb_down_foc hb hε
  intro t ht1 ht2
  have := h t ht1 ht2
  nlinarith

lemma ilb_rev_update (a b : ℝ) (q : Fin 2 → ℝ) (i : Fin 2) (x : ℝ) :
    revenue a b (Function.update q i x) i = (a - b * (x + (q 0 + q 1 - q i))) * x := by
  fin_cases i
  · simp [revenue, Function.update]
  · simp [revenue, Function.update]
    left; left; ring

/-- The equilibrium deviation inequality, written out. -/
lemma ilb_dev {a b c : ℝ} {k : Contract} {v : Fin 2 → Terms} {q : Fin 2 → ℝ}
    (hq : IsRetailerEq a b c k v q) (i : Fin 2) (x : ℝ) (hx : x ∈ feasibleSet k (v i)) :
    (a - b * (x + (q 0 + q 1 - q i))) * x
        - payment c k (v i) x ((a - b * (x + (q 0 + q 1 - q i))) * x) ≤
      (a - b * (q 0 + q 1)) * q i - payment c k (v i) (q i) ((a - b * (q 0 + q 1)) * q i) := by
  have h := hq.2 i x hx
  simp only [retailerProfit] at h
  rw [ilb_rev_update, Function.update_self] at h
  exact h

lemma ilb_pay_comp (a b c : ℝ) (k : Contract) (x r : ℝ) :
    payment c k (competitiveTerms a b c k) x r = c * x := by
  cases k <;> simp [payment, competitiveTerms]

lemma ilb_feas_comp {a b c : ℝ} (h : Standing a b c) (k : Contract) (x : ℝ) :
    x ∈ feasibleSet k (competitiveTerms a b c k) ↔ (competitiveTerms a b c k).qmin ≤ x := by
  have hL : 0 ≤ (a - c) / (4 * b) := div_nonneg (by linarith [h.2]) (by linarith [h.1])
  cases k <;> simp [feasibleSet, competitiveTerms]
  intro hx; exact le_trans hL hx

lemma ilb_qmin_comp {a b c : ℝ} (h : Standing a b c) (k : Contract) :
    0 ≤ (competitiveTerms a b c k).qmin ∧ (competitiveTerms a b c k).qmin ≤ (a - c) / (4 * b) := by
  have hL : 0 ≤ (a - c) / (4 * b) := div_nonneg (by linarith [h.2]) (by linarith [h.1])
  cases k <;> simp [competitiveTerms, hL]

theorem ilb_prop1 (a b c : ℝ) (h : Standing a b c) (k : Contract) :
    (∃ q : Fin 2 → ℝ, IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) q) ∧
    ∀ q : Fin 2 → ℝ, IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) q →
      ∀ i : Fin 2, q i = (a - c) / (3 * b) ∧
        manufacturerProfit a b c k (fun _ => competitiveTerms a b c k) q i = 0 ∧
        retailerProfit a b c k (fun _ => competitiveTerms a b c k) q i =
          (a - c) ^ 2 / (9 * b) := by
  obtain ⟨hb, hac⟩ := h
  set A := a - c with hA
  have hA0 : 0 < A := by linarith
  set L := (competitiveTerms a b c k).qmin with hLdef
  obtain ⟨hL0, hL1⟩ := ilb_qmin_comp ⟨hb, hac⟩ k
  rw [← hA] at hL1
  have hL1' : 4 * b * L ≤ A := by
    have := (le_div_iff₀ (by linarith : (0:ℝ) < 4 * b)).1 hL1; linarith
  -- the payoff of retailer `i` under the competitive terms
  have hpay := ilb_pay_comp a b c k
  have hfeas := ilb_feas_comp ⟨hb, hac⟩ k
  -- per-retailer first-order conditions
  have foc : ∀ q : Fin 2 → ℝ, IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) q →
      ∀ i : Fin 2, L ≤ q i ∧ A - b * (q 0 + q 1 - q i) - 2 * b * q i ≤ 0 ∧
        (L < q i → A - b * (q 0 + q 1 - q i) - 2 * b * q i = 0) := by
    intro q hq i
    have hqi : L ≤ q i := (hfeas (q i)).1 (hq.1 i)
    have hdev : ∀ x, L ≤ x → x * (A - b * (q 0 + q 1 - q i) - b * x) ≤
        q i * (A - b * (q 0 + q 1 - q i) - b * q i) := by
      intro x hx
      have := ilb_dev hq i x ((hfeas x).2 hx)
      simp only [hpay] at this
      linear_combination this
    refine ⟨hqi, ?_, ?_⟩
    · have := ilb_quad_up (K := A - b * (q 0 + q 1 - q i)) (q := q i) hb.le
        (fun t ht => by
          have := hdev (q i + t) (by linarith)
          linear_combination this)
      linarith
    · intro hlt
      have h1 := ilb_quad_up (K := A - b * (q 0 + q 1 - q i)) (q := q i) hb.le
        (fun t ht => by
          have := hdev (q i + t) (by linarith)
          linear_combination this)
      have h2 := ilb_quad_down (K := A - b * (q 0 + q 1 - q i)) (q := q i) hb.le
        (sub_pos.2 hlt)
        (fun t ht1 ht2 => by
          have := hdev (q i + t) (by linarith)
          linear_combination this)
      linarith
  have hq3 : 0 < 3 * b := by linarith
  constructor
  · refine ⟨fun _ => A / (3 * b), ?_, ?_⟩
    · intro i
      rw [hfeas]
      show L ≤ A / (3 * b)
      rw [le_div_iff₀ hq3]; nlinarith
    · intro i x hx
      simp only [retailerProfit]
      rw [ilb_rev_update, Function.update_self]
      simp only [hpay, revenue]
      have e : A / (3 * b) * (3 * b) = A := by field_simp
      set y := A / (3 * b)
      have ha : a = c + 3 * b * y := by linarith
      rw [ha]
      nlinarith [mul_nonneg hb.le (sq_nonneg (x - y))]
  · intro q hq
    obtain ⟨h0L, h0u, h0e⟩ := foc q hq 0
    obtain ⟨h1L, h1u, h1e⟩ := foc q hq 1
    simp only [show (q 0 + q 1 - q 0) = q 1 by ring, show (q 0 + q 1 - q 1) = q 0 by ring]
      at h0u h0e h1u h1e
    have hboth : L < q 0 ∧ L < q 1 := by
      rcases lt_or_eq_of_le h0L with h0 | h0 <;> rcases lt_or_eq_of_le h1L with h1 | h1
      · exact ⟨h0, h1⟩
      · exfalso
        have e0 := h0e h0
        rw [← h1] at h1u e0
        nlinarith
      · exfalso
        have e1 := h1e h1
        rw [← h0] at h0u e1
        nlinarith
      · exfalso
        rw [← h0, ← h1] at h0u
        nlinarith
    have e0 := h0e hboth.1
    have e1 := h1e hboth.2
    have hq0 : q 0 = A / (3 * b) := by
      rw [eq_div_iff hq3.ne']; nlinarith
    have hq1 : q 1 = A / (3 * b) := by
      rw [eq_div_iff hq3.ne']; nlinarith
    intro i
    have hqi : q i = A / (3 * b) := by fin_cases i <;> simp [hq0, hq1]
    refine ⟨hqi, ?_, ?_⟩
    · simp only [manufacturerProfit, hpay]; ring
    · simp only [retailerProfit, revenue, hpay, hq0, hq1, hqi]
      field_simp
      ring

/-! ### Retailer equilibrium under WPFF with fees `f ≤ 0` -/

theorem ilb_eq_linear (a b c w : ℝ) (hb : 0 < b) (hw : w < a) (v : Fin 2 → Terms)
    (hadm : ∀ i, Admissible c Contract.WPFF (v i)) (hvw : ∀ i, (v i).w = w)
    (hf : ∀ i, (v i).f ≤ 0) :
    (∃ q : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q) ∧
    ∀ q : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q →
      ∀ i : Fin 2, q i = (a - w) / (3 * b) ∧
        retailerProfit a b c Contract.WPFF v q i = (a - w) ^ 2 / (9 * b) - (v i).f := by
  have hfeas : ∀ i x, x ∈ feasibleSet Contract.WPFF (v i) ↔ 0 ≤ x := by
    intro i x; simp [feasibleSet]
  have hq3 : 0 < 3 * b := by linarith
  set A := a - w with hA
  have hA0 : 0 < A := by linarith
  constructor
  · refine ⟨fun _ => A / (3 * b), ?_, ?_⟩
    · intro i; rw [hfeas]; exact (div_pos hA0 hq3).le
    · intro i x hx
      rw [hfeas] at hx
      simp only [retailerProfit]
      rw [ilb_rev_update, Function.update_self]
      simp only [payment, revenue, hvw]
      have e : A / (3 * b) * (3 * b) = A := by field_simp
      have hy : 0 < A / (3 * b) := div_pos hA0 hq3
      set y := A / (3 * b)
      have ha : a = w + 3 * b * y := by linarith
      rw [ha, if_pos hy]
      rcases lt_or_eq_of_le hx with hx | hx
      · rw [if_pos hx]
        nlinarith [mul_nonneg hb.le (sq_nonneg (x - y))]
      · subst hx
        simp
        nlinarith [hf i, mul_pos hb (mul_pos hy hy)]
  · intro q hq
    -- per-retailer conditions
    have cond : ∀ i : Fin 2, 0 ≤ q i ∧
        (0 < q i → A - b * (q 0 + q 1 - q i) - 2 * b * q i = 0) ∧
        (q i = 0 → A - b * (q 0 + q 1 - q i) ≤ 0) := by
      intro i
      have hqi : 0 ≤ q i := (hfeas i (q i)).1 (hq.1 i)
      have hdev : ∀ x, 0 ≤ x → (a - b * (x + (q 0 + q 1 - q i))) * x
          - (w * x + if 0 < x then (v i).f else 0) ≤
          (a - b * (q 0 + q 1)) * q i - (w * q i + if 0 < q i then (v i).f else 0) := by
        intro x hx
        have := ilb_dev hq i x ((hfeas i x).2 hx)
        simpa only [payment, hvw] using this
      refine ⟨hqi, ?_, ?_⟩
      · intro hpos
        have hpos' : ∀ x, 0 < x → x * (A - b * (q 0 + q 1 - q i) - b * x) ≤
            q i * (A - b * (q 0 + q 1 - q i) - b * q i) := by
          intro x hx
          have := hdev x hx.le
          rw [if_pos hx, if_pos hpos] at this
          linear_combination this
        have h1 := ilb_quad_up (K := A - b * (q 0 + q 1 - q i)) (q := q i) hb.le
          (fun t ht => by
            have := hpos' (q i + t) (by linarith)
            linear_combination this)
        have h2 := ilb_quad_down (K := A - b * (q 0 + q 1 - q i)) (q := q i) hb.le hpos
          (fun t ht1 ht2 => by
            have := hpos' (q i + t) (by linarith)
            linear_combination this)
        linarith
      · intro h0
        apply ilb_up_foc hb.le
        intro t ht
        have := hdev t ht.le
        rw [if_pos ht, h0] at this
        simp at this
        rw [h0, hA]
        nlinarith [hf i]
    obtain ⟨h0n, h0p, h0z⟩ := cond 0
    obtain ⟨h1n, h1p, h1z⟩ := cond 1
    simp only [show (q 0 + q 1 - q 0) = q 1 by ring, show (q 0 + q 1 - q 1) = q 0 by ring]
      at h0p h0z h1p h1z
    have hboth : 0 < q 0 ∧ 0 < q 1 := by
      rcases lt_or_eq_of_le h0n with h0 | h0 <;> rcases lt_or_eq_of_le h1n with h1 | h1
      · exact ⟨h0, h1⟩
      · exfalso
        have e0 := h0p h0
        have z1 := h1z h1.symm
        rw [← h1] at e0
        nlinarith
      · exfalso
        have e1 := h1p h1
        have z0 := h0z h0.symm
        rw [← h0] at e1
        nlinarith
      · exfalso
        have z0 := h0z h0.symm
        rw [← h1] at z0
        linarith
    have e0 := h0p hboth.1
    have e1 := h1p hboth.2
    have hq0 : q 0 = A / (3 * b) := by
      rw [eq_div_iff hq3.ne']; nlinarith
    have hq1 : q 1 = A / (3 * b) := by
      rw [eq_div_iff hq3.ne']; nlinarith
    intro i
    have hqi : q i = A / (3 * b) := by fin_cases i <;> simp [hq0, hq1]
    refine ⟨hqi, ?_⟩
    have hy : 0 < A / (3 * b) := div_pos hA0 hq3
    simp only [retailerProfit, revenue, payment, hvw, hq0, hq1, hqi, if_pos hy]
    field_simp
    ring

end IllinoisBrick.Cartel

open IllinoisBrick.Cartel

theorem solution (a b c w : ℝ) (hb : 0 < b) (hw : w < a) (v : Fin 2 → Terms)
    (hadm : ∀ i, Admissible c Contract.WPFF (v i)) (hvw : ∀ i, (v i).w = w)
    (hf : ∀ i, (v i).f ≤ 0) :
    (∃ q : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q) ∧
    ∀ q : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q →
      ∀ i : Fin 2, q i = (a - w) / (3 * b) ∧
        retailerProfit a b c Contract.WPFF v q i = (a - w) ^ 2 / (9 * b) - (v i).f :=
  ilb_eq_linear a b c w hb hw v hadm hvw hf
