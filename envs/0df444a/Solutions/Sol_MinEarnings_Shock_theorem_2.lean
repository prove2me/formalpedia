-- Prove2me | solution 1 for MinEarnings.Shock.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:08:50.133198+00:00
-- url     : https://prove2.me/submissions/d46a5f7c-6afa-490e-be61-819e920aa659

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

lemma mea_theorem_2 (D S : ℝ → ℝ) (pStar wStar M u₀ q : ℝ) (hA : Assumptions D S pStar wStar)
    (hM : 0 < M) (hu₀ : 0 < u₀) (hu₀1 : u₀ ≤ 1) (hq : pStar ≤ q)
    (hRq : revenue D q = cost S M) :
    AbsorbsShock D S M u₀ ↔ M / q ≤ u₀ := by
  have hqpos := mea_q_pos D S pStar wStar M q hA hM hq hRq
  constructor
  swap
  · intro hge
    obtain ⟨h1, h2, h3⟩ := mea_absorb D S pStar wStar M u₀ q hA hM hu₀1 hq hRq hge
    refine ⟨fun _ => q, fun _ => q, fun _ => M, fun _ => ⟨hqpos.le, hqpos.le⟩, ?_, ?_, ?_,
      ⟨q, fun _ => le_rfl⟩, ?_⟩
    · intro t
      exact ⟨hM, by show M = q * util D S q M; exact h3⟩
    · intro t
      show M / util D S q M ≤ q
      rw [← h2, ← h1]
      field_simp
      exact le_rfl
    · show M / u₀ ≤ q
      rw [div_le_iff₀ hu₀]
      rw [div_le_iff₀ hqpos] at hge
      linarith
    · intro t
      show 0 ≤ (q - q) * quantity D S q M
      simp
  · rintro ⟨p, w, z, hf, he, hr, hw0, ⟨B, hB⟩, hprof⟩
    by_contra hlt
    push_neg at hlt
    have hqM : q < M / u₀ := by
      rw [lt_div_iff₀ hu₀]
      have := (lt_div_iff₀ hqpos).1 hlt
      linarith
    have hqw0 : q < w 0 := hqM.trans_le hw0
    have hw0pos : 0 < w 0 := hqpos.trans hqw0
    have hpw : ∀ s, w s ≤ p s := by
      intro s
      have h1 := hprof s
      have hQ : 0 < quantity D S (p s) (z s) :=
        lt_min (hA.D_pos _ (hf s).1) (hA.S_pos _ (he s).1)
      by_contra hlt
      push_neg at hlt
      have : (p s - w s) * quantity D S (p s) (z s) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hQ
      exact absurd h1 (not_le.2 this)
    -- the level ζ with cost ζ = R(w 0)
    have hRw0 : revenue D (w 0) < cost S M := by
      rw [← hRq]
      exact hA.revenue_strictAntiOn (Set.mem_Ici.2 hq) (Set.mem_Ici.2 (hq.trans hqw0.le)) hqw0
    have hRpos : 0 < revenue D (w 0) := mul_pos hw0pos (hA.D_pos _ hw0pos.le)
    have hcont : ContinuousOn (cost S) (Set.Icc 0 M) := by
      unfold cost
      exact continuousOn_id.mul (hA.S_continuousOn.mono (fun x hx => Set.mem_Ici.2 hx.1))
    have hc0 : cost S 0 = 0 := by simp [cost]
    obtain ⟨ζ, hζ, hζc⟩ := intermediate_value_Icc hM.le hcont
      (show revenue D (w 0) ∈ Set.Icc (cost S 0) (cost S M) from ⟨by rw [hc0]; exact hRpos.le, hRw0.le⟩)
    have hζpos : 0 < ζ := by
      rcases hζ.1.eq_or_lt with h | h
      · exfalso; rw [← h, hc0] at hζc; linarith
      · exact h
    have hζM : ζ < M := by
      rcases hζ.2.eq_or_lt with h | h
      · exfalso; rw [h] at hζc; linarith
      · exact h
    set φ : ℝ := M / ζ with hφ
    have hφ1 : 1 < φ := by rw [hφ, lt_div_iff₀ hζpos]; linarith
    have hind : ∀ t, φ ^ t * w 0 ≤ w t := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have hwt : w 0 ≤ w t := by
          calc w 0 = 1 * w 0 := (one_mul _).symm
            _ ≤ φ ^ t * w 0 :=
              mul_le_mul_of_nonneg_right (one_le_pow₀ hφ1.le) hw0pos.le
            _ ≤ w t := ih
        have hg := mea_growth D S pStar wStar M hA p w z hf he hr t (hpw t) (w 0) ζ
          (hq.trans hqw0.le) hwt hζpos hζc
        have : φ * w t ≤ w (t + 1) := by
          rw [hφ, div_mul_eq_mul_div, div_le_iff₀ hζpos]
          exact hg
        calc φ ^ (t + 1) * w 0 = φ * (φ ^ t * w 0) := by ring
          _ ≤ φ * w t := mul_le_mul_of_nonneg_left ih (by linarith)
          _ ≤ w (t + 1) := this
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / w 0) hφ1
    have h1 : B < φ ^ n * w 0 := by
      rwa [div_lt_iff₀ hw0pos] at hn
    have := hB n
    have := hind n
    linarith

theorem solution (D S : ℝ → ℝ) (pStar wStar M u₀ q : ℝ) (hA : MinEarnings.Threshold.Assumptions D S pStar wStar)
    (hM : 0 < M) (hu₀ : 0 < u₀) (hu₀1 : u₀ ≤ 1) (hq : pStar ≤ q)
    (hRq : MinEarnings.Threshold.revenue D q = MinEarnings.Threshold.cost S M) :
    AbsorbsShock D S M u₀ ↔ M / q ≤ u₀ :=
  mea_theorem_2 D S pStar wStar M u₀ q hA hM hu₀ hu₀1 hq hRq
