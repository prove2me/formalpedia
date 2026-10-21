-- Prove2me | solution 1 for MinEarnings.Shock.wage_growth
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:18:48.68735+00:00
-- url     : https://prove2.me/submissions/ea02bdfa-d8a3-468f-a7c5-00c861c8c678

import Mathlib
import Definitions.Def_MinEarnings_Shock_Setting

set_option autoImplicit false
open MinEarnings.Threshold MinEarnings.Shock

lemma mea_util_pos (D S : ℝ → ℝ) (hP : Primitives D S) {p z : ℝ} (hp : 0 ≤ p) (hz : 0 < z) :
    0 < util D S p z := by
  unfold util quantity
  exact div_pos (lt_min (hP.D_pos p hp) (hP.S_pos z hz)) (hP.S_pos z hz)

lemma mea_cost_lt (D S : ℝ → ℝ) (hP : Primitives D S) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    cost S a < cost S b := by
  unfold cost
  have h1 : S a < S b :=
    hP.S_strictMonoOn (Set.mem_Ici.2 ha.le) (Set.mem_Ici.2 (ha.trans hab).le) hab
  have h3 := hP.S_pos b (ha.trans hab)
  nlinarith [mul_pos (sub_pos.2 hab) h3, mul_pos ha (sub_pos.2 h1)]

lemma mea_cost_le (D S : ℝ → ℝ) (hP : Primitives D S) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    cost S a ≤ cost S b := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · exact (mea_cost_lt D S hP ha h).le

lemma mea_le_of_cost_le (D S : ℝ → ℝ) (hP : Primitives D S) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : cost S a ≤ cost S b) : a ≤ b := by
  by_contra hc
  push_neg at hc
  have := mea_cost_lt D S hP hb hc
  linarith

lemma mea_lt_of_cost_lt (D S : ℝ → ℝ) (hP : Primitives D S) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : cost S a < cost S b) : a < b := by
  by_contra hc
  push_neg at hc
  have := mea_cost_le D S hP hb hc
  linarith

lemma mea_q_pos (D S : ℝ → ℝ) (pStar wStar M q : ℝ) (hA : Assumptions D S pStar wStar)
    (hM : 0 < M) (hq : pStar ≤ q) (hRq : revenue D q = cost S M) : 0 < q := by
  have hq0 : 0 ≤ q := hA.pStar_nonneg.trans hq
  rcases hq0.eq_or_lt with h | h
  · exfalso
    have h1 : cost S M = 0 := by rw [← hRq, ← h]; simp [revenue]
    have h2 : 0 < cost S M := mul_pos hM (hA.S_pos M hM)
    linarith
  · exact h

lemma mea_step (D S : ℝ → ℝ) (M : ℝ) (hP : Primitives D S) (p w z : ℕ → ℝ)
    (hf : IsFeasible p w) (he : IsEquilibrium D S p w z) (hr : MinEarningsRule D S M p w z)
    (t : ℕ) (hpw : w t ≤ p t) :
    0 < w t ∧ cost S (z t) ≤ revenue D (w t) ∧ M * w t ≤ w (t + 1) * z t := by
  have hp0 := (hf t).1
  have hw0 := (hf t).2
  obtain ⟨hzpos, hzeq⟩ := he t
  have hup := mea_util_pos D S hP hp0 hzpos
  have hwpos : 0 < w t := by
    rcases hw0.eq_or_lt with h | h
    · rw [← h] at hzeq; simp at hzeq; linarith
    · exact h
  refine ⟨hwpos, ?_, ?_⟩
  · have hS := hP.S_pos (z t) hzpos
    have hDle : D (p t) ≤ D (w t) :=
      hP.D_strictAntiOn.antitoneOn (Set.mem_Ici.2 hw0) (Set.mem_Ici.2 hp0) hpw
    have hu : util D S (p t) (z t) * S (z t) = min (D (p t)) (S (z t)) := by
      unfold util quantity
      field_simp
    unfold cost revenue
    calc z t * S (z t) = (w t * util D S (p t) (z t)) * S (z t) := by rw [← hzeq]
      _ = w t * min (D (p t)) (S (z t)) := by rw [mul_assoc, hu]
      _ ≤ w t * D (p t) := mul_le_mul_of_nonneg_left (min_le_left _ _) hw0
      _ ≤ w t * D (w t) := mul_le_mul_of_nonneg_left hDle hw0
  · have := hr t
    rw [div_le_iff₀ hup] at this
    calc M * w t ≤ (w (t + 1) * util D S (p t) (z t)) * w t :=
          mul_le_mul_of_nonneg_right this hwpos.le
      _ = w (t + 1) * (w t * util D S (p t) (z t)) := by ring
      _ = w (t + 1) * z t := by rw [← hzeq]

/-- one growth step: if `w t ≥ a ≥ p*` and `ζ > 0` has cost `R(a)`, then `M w_t ≤ w_{t+1} ζ`. -/
lemma mea_growth (D S : ℝ → ℝ) (pStar wStar M : ℝ) (hA : Assumptions D S pStar wStar)
    (p w z : ℕ → ℝ)
    (hf : IsFeasible p w) (he : IsEquilibrium D S p w z) (hr : MinEarningsRule D S M p w z)
    (t : ℕ) (hpw : w t ≤ p t) (a ζ : ℝ) (ha : pStar ≤ a) (hat : a ≤ w t) (hζ : 0 < ζ)
    (hζa : cost S ζ = revenue D a) : M * w t ≤ w (t + 1) * ζ := by
  obtain ⟨hwpos, hC, hM⟩ := mea_step D S M hA.toPrimitives p w z hf he hr t hpw
  have hR : revenue D (w t) ≤ revenue D a :=
    hA.revenue_strictAntiOn.antitoneOn (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (ha.trans hat)) hat
  have hzt : z t ≤ ζ :=
    mea_le_of_cost_le D S hA.toPrimitives (he t).1 hζ (by rw [hζa]; exact hC.trans hR)
  have hw1 : 0 ≤ w (t + 1) := (hf (t + 1)).2
  calc M * w t ≤ w (t + 1) * z t := hM
    _ ≤ w (t + 1) * ζ := mul_le_mul_of_nonneg_left hzt hw1

lemma mea_absorb (D S : ℝ → ℝ) (pStar wStar M u₀ q : ℝ) (hA : Assumptions D S pStar wStar)
    (hM : 0 < M) (hu₀1 : u₀ ≤ 1) (hq : pStar ≤ q) (hRq : revenue D q = cost S M)
    (hge : M / q ≤ u₀) :
    M / q = D q / S M ∧ D q / S M = util D S q M ∧ M = q * util D S q M := by
  have hqpos := mea_q_pos D S pStar wStar M q hA hM hq hRq
  have hSM := hA.S_pos M hM
  have h1 : M / q = D q / S M := by
    rw [div_eq_div_iff hqpos.ne' hSM.ne']
    have : q * D q = M * S M := hRq
    linarith
  have hle : D q ≤ S M := by
    have : D q / S M ≤ 1 := by rw [← h1]; exact hge.trans hu₀1
    rwa [div_le_one hSM] at this
  have h2 : D q / S M = util D S q M := by
    unfold util quantity
    rw [min_eq_left hle]
  refine ⟨h1, h2, ?_⟩
  rw [← h2, ← h1]
  field_simp

lemma mea_phi (D S H : ℝ → ℝ) (pStar wStar M u₀ q : ℝ) (hA : Assumptions D S pStar wStar)
    (hH : IsCostInverse S H) (hM : 0 < M) (hu₀ : 0 < u₀)
    (hq : pStar ≤ q) (hRq : revenue D q = cost S M) (hlt : u₀ < M / q) (w₁ : ℝ)
    (hw₁ : M / u₀ ≤ w₁) :
    M / H (revenue D (M / u₀)) ≤ M / H (revenue D w₁) ∧ 1 < M / H (revenue D (M / u₀)) := by
  have hqpos := mea_q_pos D S pStar wStar M q hA hM hq hRq
  have hqM : q < M / u₀ := by
    rw [lt_div_iff₀ hu₀]
    have := (lt_div_iff₀ hqpos).1 hlt
    linarith
  have hMu : 0 < M / u₀ := hqpos.trans hqM
  have hw₁pos : 0 < w₁ := hMu.trans_le hw₁
  have hRpos : ∀ x, 0 < x → 0 < revenue D x := fun x hx =>
    mul_pos hx (hA.D_pos x hx.le)
  have hR1 : revenue D w₁ ≤ revenue D (M / u₀) :=
    hA.revenue_strictAntiOn.antitoneOn (Set.mem_Ici.2 (hq.trans hqM.le)) (Set.mem_Ici.2 (hq.trans (hqM.le.trans hw₁))) hw₁
  obtain ⟨hH1, hH1c⟩ := hH (revenue D (M / u₀)) (hRpos _ hMu)
  obtain ⟨hH2, hH2c⟩ := hH (revenue D w₁) (hRpos _ hw₁pos)
  constructor
  · have : H (revenue D w₁) ≤ H (revenue D (M / u₀)) :=
      mea_le_of_cost_le D S hA.toPrimitives hH2 hH1 (by rw [hH1c, hH2c]; exact hR1)
    exact div_le_div_of_nonneg_left hM.le hH2 this
  · have hRlt : revenue D (M / u₀) < revenue D q :=
      hA.revenue_strictAntiOn (Set.mem_Ici.2 hq) (Set.mem_Ici.2 (hq.trans hqM.le)) hqM
    have : H (revenue D (M / u₀)) < M :=
      mea_lt_of_cost_lt D S hA.toPrimitives hH1 hM (by rw [hH1c]; rw [← hRq]; exact hRlt)
    rw [lt_div_iff₀ hH1]
    linarith

lemma mea_wage_growth (D S H : ℝ → ℝ) (pStar wStar M u₀ q : ℝ) (hA : Assumptions D S pStar wStar)
    (hH : IsCostInverse S H) (hM : 0 < M) (hu₀ : 0 < u₀)
    (hq : pStar ≤ q) (hRq : revenue D q = cost S M) (hlt : u₀ < M / q)
    (w z : ℕ → ℝ) (hfeas : IsFeasible w w) (heq : IsEquilibrium D S w w z)
    (hrule : MinEarningsRule D S M w w z) (hw0 : M / u₀ ≤ w 0) :
    (∀ t, M / H (revenue D (M / u₀)) * w t ≤ w (t + 1)) ∧
      ∀ t, (M / H (revenue D (M / u₀))) ^ t * w 0 ≤ w t := by
  have hqpos := mea_q_pos D S pStar wStar M q hA hM hq hRq
  have hqM : q < M / u₀ := by
    rw [lt_div_iff₀ hu₀]
    have := (lt_div_iff₀ hqpos).1 hlt
    linarith
  have hMu : 0 < M / u₀ := hqpos.trans hqM
  have hRpos : 0 < revenue D (M / u₀) := mul_pos hMu (hA.D_pos _ hMu.le)
  obtain ⟨hH1, hH1c⟩ := hH (revenue D (M / u₀)) hRpos
  obtain ⟨-, hφ1⟩ := mea_phi D S H pStar wStar M u₀ q hA hH hM hu₀ hq hRq hlt (w 0) hw0
  set φ : ℝ := M / H (revenue D (M / u₀)) with hφ
  have hw0pos : 0 < w 0 := hMu.trans_le hw0
  have step : ∀ t, M / u₀ ≤ w t → φ * w t ≤ w (t + 1) := by
    intro t ht
    have hg := mea_growth D S pStar wStar M hA w w z hfeas heq hrule t le_rfl (M / u₀)
      (H (revenue D (M / u₀))) (hq.trans hqM.le) ht hH1 hH1c
    rw [hφ, div_mul_eq_mul_div, div_le_iff₀ hH1]
    exact hg
  have hind : ∀ t, φ ^ t * w 0 ≤ w t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hwt : M / u₀ ≤ w t := by
        calc M / u₀ ≤ w 0 := hw0
          _ = 1 * w 0 := (one_mul _).symm
          _ ≤ φ ^ t * w 0 := mul_le_mul_of_nonneg_right (one_le_pow₀ hφ1.le) hw0pos.le
          _ ≤ w t := ih
      calc φ ^ (t + 1) * w 0 = φ * (φ ^ t * w 0) := by ring
        _ ≤ φ * w t := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ w (t + 1) := step t hwt
  refine ⟨fun t => step t ?_, hind⟩
  calc M / u₀ ≤ w 0 := hw0
    _ = 1 * w 0 := (one_mul _).symm
    _ ≤ φ ^ t * w 0 := mul_le_mul_of_nonneg_right (one_le_pow₀ hφ1.le) hw0pos.le
    _ ≤ w t := hind t

theorem solution (D S H : ℝ → ℝ) (pStar wStar M u₀ q : ℝ)
    (hA : MinEarnings.Threshold.Assumptions D S pStar wStar) (hH : MinEarnings.Threshold.IsCostInverse S H) (hM : 0 < M) (hu₀ : 0 < u₀)
    (hu₀1 : u₀ ≤ 1) (hq : pStar ≤ q) (hRq : MinEarnings.Threshold.revenue D q = MinEarnings.Threshold.cost S M) (hlt : u₀ < M / q)
    (w z : ℕ → ℝ) (hfeas : MinEarnings.Threshold.IsFeasible w w) (heq : MinEarnings.Threshold.IsEquilibrium D S w w z)
    (hrule : MinEarnings.Threshold.MinEarningsRule D S M w w z) (hw0 : M / u₀ ≤ w 0) :
    (∀ t, M / H (MinEarnings.Threshold.revenue D (M / u₀)) * w t ≤ w (t + 1)) ∧
      ∀ t, (M / H (MinEarnings.Threshold.revenue D (M / u₀))) ^ t * w 0 ≤ w t :=
  mea_wage_growth D S H pStar wStar M u₀ q hA hH hM hu₀ hq hRq hlt w z hfeas heq hrule hw0
