-- Prove2me | solution 1 for LaborWelfare.PoolSize.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T16:12:59.649583+00:00
-- url     : https://prove2.me/submissions/cf1d0cc5-a45e-4944-b10b-3775be255817

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

set_option autoImplicit false

namespace LW079

/-! ## Part C: the first-order-condition curve `s (1 - s) = k(ρ)` (pure real analysis). -/

noncomputable def qf (β ρ : ℝ) : ℝ := ((1 - ρ) ^ 2)⁻¹ + β * (1 - ρ)⁻¹
noncomputable def qd (β ρ : ℝ) : ℝ := 2 * ((1 - ρ) ^ 3)⁻¹ + β * ((1 - ρ) ^ 2)⁻¹
noncomputable def K2 (C β ρ : ℝ) : ℝ := C * ρ ^ (β - 1) * qf β ρ
noncomputable def kf (C β ρ : ℝ) : ℝ := C * ρ ^ (β - 1) * ρ ^ 2 * qf β ρ
noncomputable def kd (C β ρ : ℝ) : ℝ := C * ρ ^ (β - 1) * ρ * ((β + 1) * qf β ρ + ρ * qd β ρ)
noncomputable def Bq (β ρ : ℝ) : ℝ := (β + 1) * qf β ρ + ρ * qd β ρ
noncomputable def Gk (C β ρ : ℝ) : ℝ := C * ρ ^ (β - 1) * ρ ^ 2 * Bq β ρ
noncomputable def Nf (K s ρ : ℝ) : ℝ := K * (1 - s) / (s * ρ ^ 2)
noncomputable def phi (C β ρ : ℝ) : ℝ := ρ * (1 + Real.sqrt (1 - 4 * kf C β ρ))
noncomputable def psi (C β ρ : ℝ) : ℝ :=
  Real.sqrt (1 - 4 * kf C β ρ) + (1 - 4 * kf C β ρ) - 2 * Gk C β ρ

lemma qf_pos {β ρ : ℝ} (hβ : 0 ≤ β) (hρ : ρ < 1) : 0 < qf β ρ := by
  unfold qf
  have h1 : 0 < 1 - ρ := by linarith
  have : 0 ≤ β * (1 - ρ)⁻¹ := mul_nonneg hβ (inv_nonneg.2 h1.le)
  have : 0 < ((1 - ρ) ^ 2)⁻¹ := by positivity
  linarith

lemma qd_pos {β ρ : ℝ} (hβ : 0 ≤ β) (hρ : ρ < 1) : 0 < qd β ρ := by
  unfold qd
  have h1 : 0 < 1 - ρ := by linarith
  have : 0 ≤ β * ((1 - ρ) ^ 2)⁻¹ := mul_nonneg hβ (by positivity)
  have : 0 < 2 * ((1 - ρ) ^ 3)⁻¹ := by positivity
  linarith

lemma inv_pow_lt {a b : ℝ} (n : ℕ) (hn : n ≠ 0) (hab : a < b) (hb : b < 1) :
    ((1 - a) ^ n)⁻¹ < ((1 - b) ^ n)⁻¹ := by
  have hb1 : 0 < 1 - b := by linarith
  apply inv_strictAnti₀ (by positivity)
  exact pow_lt_pow_left₀ (by linarith) hb1.le hn

lemma inv_pow_le {a b : ℝ} (n : ℕ) (hab : a ≤ b) (hb : b < 1) :
    ((1 - a) ^ n)⁻¹ ≤ ((1 - b) ^ n)⁻¹ := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  exact (inv_pow_lt n hn.ne' h hb).le

lemma qf_lt {β a b : ℝ} (hβ : 0 ≤ β) (hab : a < b) (hb : b < 1) : qf β a < qf β b := by
  unfold qf
  have e1 := inv_pow_lt 2 (by norm_num) hab hb
  have e2 := inv_pow_le 1 hab.le hb
  simp only [pow_one] at e2
  have : β * (1 - a)⁻¹ ≤ β * (1 - b)⁻¹ := mul_le_mul_of_nonneg_left e2 hβ
  linarith

lemma qd_le {β a b : ℝ} (hβ : 0 ≤ β) (hab : a ≤ b) (hb : b < 1) : qd β a ≤ qd β b := by
  unfold qd
  have e1 := inv_pow_le 3 hab hb
  have e2 := inv_pow_le 2 hab hb
  have : β * ((1 - a) ^ 2)⁻¹ ≤ β * ((1 - b) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left e2 hβ
  linarith

lemma Bq_pos {β ρ : ℝ} (hβ : 0 ≤ β) (h0 : 0 ≤ ρ) (hρ : ρ < 1) : 0 < Bq β ρ := by
  unfold Bq
  have := qf_pos hβ hρ
  have := qd_pos hβ hρ
  have : 0 ≤ ρ * qd β ρ := mul_nonneg h0 (qd_pos hβ hρ).le
  nlinarith

lemma Bq_le {β a b : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    Bq β a ≤ Bq β b := by
  unfold Bq
  have h1 : qf β a ≤ qf β b := by
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact (qf_lt hβ h hb).le
  have h2 := qd_le hβ hab hb
  have h3 := qd_pos hβ (show a < 1 by linarith)
  have : a * qd β a ≤ b * qd β b := mul_le_mul hab h2 h3.le (by linarith)
  have : (β + 1) * qf β a ≤ (β + 1) * qf β b := mul_le_mul_of_nonneg_left h1 (by linarith)
  linarith

lemma kf_eq (C β ρ : ℝ) : kf C β ρ = ρ ^ 2 * K2 C β ρ := by unfold kf K2; ring

lemma K2_nonneg {C β a : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (ha : 0 ≤ a) (ha1 : a < 1) :
    0 ≤ K2 C β a := by
  unfold K2
  exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg ha _)) (qf_pos (by linarith) ha1).le

lemma K2_lt {C β a b : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    K2 C β a < K2 C β b := by
  unfold K2
  have h1 : a ^ (β - 1) ≤ b ^ (β - 1) := Real.rpow_le_rpow ha hab.le (by linarith)
  have h2 : 0 < b ^ (β - 1) := Real.rpow_pos_of_pos (by linarith) _
  have hq1 := qf_pos (β := β) (by linarith) (show a < 1 by linarith)
  have hq2 := qf_lt (β := β) (by linarith) hab hb
  calc C * a ^ (β - 1) * qf β a ≤ C * b ^ (β - 1) * qf β a := by
        apply mul_le_mul_of_nonneg_right _ hq1.le
        exact mul_le_mul_of_nonneg_left h1 hC.le
    _ < C * b ^ (β - 1) * qf β b := mul_lt_mul_of_pos_left hq2 (mul_pos hC h2)

lemma kf_zero (C β : ℝ) : kf C β 0 = 0 := by unfold kf; simp

lemma kf_nonneg {C β a : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (ha : 0 ≤ a) (ha1 : a < 1) :
    0 ≤ kf C β a := by
  rw [kf_eq]; exact mul_nonneg (sq_nonneg a) (K2_nonneg hC hβ ha ha1)

lemma kf_lt {C β a b : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    kf C β a < kf C β b := by
  rw [kf_eq, kf_eq]
  have hK := K2_lt hC hβ ha hab hb
  have hK0 := K2_nonneg hC hβ ha (by linarith)
  have hsq : a ^ 2 < b ^ 2 := by nlinarith
  calc a ^ 2 * K2 C β a ≤ b ^ 2 * K2 C β a := mul_le_mul_of_nonneg_right hsq.le hK0
    _ < b ^ 2 * K2 C β b := mul_lt_mul_of_pos_left hK (by nlinarith)

lemma kf_pos {C β a : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (ha : 0 < a) (ha1 : a < 1) :
    0 < kf C β a := by
  have := kf_lt hC hβ le_rfl ha ha1; rwa [kf_zero] at this

lemma kf_lt_iff {C β a b : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (ha : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 ≤ b) (hb1 : b < 1) : kf C β a < kf C β b ↔ a < b := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rcases eq_or_lt_of_le hc with e | e
    · rw [e] at h; exact lt_irrefl _ h
    · exact lt_asymm h (kf_lt hC hβ hb e ha1)
  · intro h; exact kf_lt hC hβ ha h hb1

lemma kf_inj {C β a b : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (ha : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 ≤ b) (hb1 : b < 1) (h : kf C β a = kf C β b) : a = b := by
  rcases lt_trichotomy a b with e | e | e
  · have := kf_lt hC hβ ha e hb1; linarith
  · exact e
  · have := kf_lt hC hβ hb e ha1; linarith

lemma Gk_lt {C β a b : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    Gk C β a < Gk C β b := by
  unfold Gk
  have h1 : a ^ (β - 1) ≤ b ^ (β - 1) := Real.rpow_le_rpow ha hab.le (by linarith)
  have h2 : 0 < b ^ (β - 1) := Real.rpow_pos_of_pos (by linarith) _
  have h0 : 0 ≤ a ^ (β - 1) := Real.rpow_nonneg ha _
  have hB1 := Bq_pos (β := β) (by linarith) ha (show a < 1 by linarith)
  have hB2 := Bq_le (β := β) (by linarith) ha hab.le hb
  have hsq : a ^ 2 < b ^ 2 := by nlinarith
  have e1 : C * a ^ (β - 1) * a ^ 2 ≤ C * b ^ (β - 1) * a ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC.le) (sq_nonneg a)
  have e2 : C * b ^ (β - 1) * a ^ 2 < C * b ^ (β - 1) * b ^ 2 :=
    mul_lt_mul_of_pos_left hsq (mul_pos hC h2)
  have e3 : 0 ≤ C * a ^ (β - 1) * a ^ 2 := mul_nonneg (mul_nonneg hC.le h0) (sq_nonneg a)
  calc C * a ^ (β - 1) * a ^ 2 * Bq β a ≤ C * b ^ (β - 1) * a ^ 2 * Bq β a :=
        mul_le_mul_of_nonneg_right e1 hB1.le
    _ < C * b ^ (β - 1) * b ^ 2 * Bq β a := mul_lt_mul_of_pos_right e2 hB1
    _ ≤ C * b ^ (β - 1) * b ^ 2 * Bq β b :=
        mul_le_mul_of_nonneg_left hB2 (by positivity)

lemma Gk_zero (C β : ℝ) : Gk C β 0 = 0 := by unfold Gk; simp

/-- Points of the FOC curve. -/
structure CP (C β s ρ : ℝ) : Prop where
  s0 : 0 < s
  s1 : s < 1
  r0 : 0 < ρ
  r1 : ρ < 1
  eq : s * (1 - s) = kf C β ρ

lemma curve_lt {C β K s1 s2 ρ1 ρ2 : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (hK : 0 < K)
    (p1 : CP C β s1 ρ1) (p2 : CP C β s2 ρ2) (hs : s1 < s2) :
    Nf K s2 ρ2 < Nf K s1 ρ1 := by
  obtain ⟨hs1, hs1', hρ1, hρ1', h1⟩ := p1
  obtain ⟨hs2p, hs2, hρ2, hρ2', h2⟩ := p2
  unfold Nf
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  suffices H : (1 - s2) * (s1 * ρ1 ^ 2) < (1 - s1) * (s2 * ρ2 ^ 2) by
    calc K * (1 - s2) * (s1 * ρ1 ^ 2) = K * ((1 - s2) * (s1 * ρ1 ^ 2)) := by ring
      _ < K * ((1 - s1) * (s2 * ρ2 ^ 2)) := mul_lt_mul_of_pos_left H hK
      _ = K * (1 - s1) * (s2 * ρ2 ^ 2) := by ring
  rcases le_or_gt ρ1 ρ2 with hρ | hρ
  · have : ρ1 ^ 2 ≤ ρ2 ^ 2 := by nlinarith
    have hA : 0 ≤ (1 - s2) * s1 := mul_nonneg (by linarith) hs1.le
    have hlt : (1 - s2) * s1 < (1 - s1) * s2 := by nlinarith
    calc (1 - s2) * (s1 * ρ1 ^ 2) = ((1 - s2) * s1) * ρ1 ^ 2 := by ring
      _ ≤ ((1 - s2) * s1) * ρ2 ^ 2 := mul_le_mul_of_nonneg_left this hA
      _ < ((1 - s1) * s2) * ρ2 ^ 2 := mul_lt_mul_of_pos_right hlt (by positivity)
      _ = (1 - s1) * (s2 * ρ2 ^ 2) := by ring
  · have hKl := K2_lt hC hβ hρ2.le hρ hρ1'
    have hB : 0 < K2 C β ρ2 := by
      have := kf_pos hC hβ hρ2 hρ2'
      rw [kf_eq] at this
      exact pos_of_mul_pos_right this (sq_nonneg _)
    rw [kf_eq] at h1 h2
    generalize K2 C β ρ1 = A at *
    generalize K2 C β ρ2 = B at *
    have hA : 0 < A := by linarith
    have key : s1 ^ 2 * B < s2 ^ 2 * A := by
      have : s1 ^ 2 < s2 ^ 2 := by nlinarith
      calc s1 ^ 2 * B < s2 ^ 2 * B := mul_lt_mul_of_pos_right this hB
        _ < s2 ^ 2 * A := mul_lt_mul_of_pos_left hKl (by positivity)
    have hp : 0 < (1 - s1) * (1 - s2) := mul_pos (by linarith) (by linarith)
    have e : ((1 - s1) * (s2 * ρ2 ^ 2) - (1 - s2) * (s1 * ρ1 ^ 2)) * (A * B)
        = (1 - s1) * (1 - s2) * (s2 ^ 2 * A - s1 ^ 2 * B) := by
      linear_combination (-(1 - s1) * s2 * A) * h2 + ((1 - s2) * s1 * B) * h1
    have h3 : 0 < ((1 - s1) * (s2 * ρ2 ^ 2) - (1 - s2) * (s1 * ρ1 ^ 2)) * (A * B) := by
      rw [e]; exact mul_pos hp (by linarith)
    by_contra hc
    push Not at hc
    have : ((1 - s1) * (s2 * ρ2 ^ 2) - (1 - s2) * (s1 * ρ1 ^ 2)) * (A * B) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (mul_pos hA hB).le
    linarith

lemma cmp {C β K s1 s2 ρ1 ρ2 : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (hK : 0 < K)
    (p1 : CP C β s1 ρ1) (p2 : CP C β s2 ρ2) (hN : Nf K s1 ρ1 < Nf K s2 ρ2) : s2 < s1 := by
  by_contra hc
  push Not at hc
  rcases eq_or_lt_of_le hc with h | h
  · have hk : kf C β ρ1 = kf C β ρ2 := by rw [← p1.eq, ← p2.eq, h]
    have := kf_inj hC hβ p1.r0.le p1.r1 p2.r0.le p2.r1 hk
    rw [h, this] at hN
    exact lt_irrefl _ hN
  · exact lt_asymm hN (curve_lt hC hβ hK p1 p2 h)

lemma Nf_pos {C β K s ρ : ℝ} (hK : 0 < K) (p : CP C β s ρ) : 0 < Nf K s ρ := by
  unfold Nf
  have := p.s0; have := p.s1; have := p.r0
  have : 0 < 1 - s := by linarith
  positivity

/-! Continuity and derivatives. -/

lemma one_sub_ne {ρ : ℝ} (hρ : ρ < 1) : (1 : ℝ) - ρ ≠ 0 := by
  intro h; linarith

lemma qf_contAt {β ρ : ℝ} (hρ : ρ < 1) : ContinuousAt (qf β) ρ := by
  have h1 := one_sub_ne hρ
  have hs : ContinuousAt (fun x : ℝ => 1 - x) ρ := continuousAt_const.sub continuousAt_id
  show ContinuousAt (fun x => ((1 - x) ^ 2)⁻¹ + β * (1 - x)⁻¹) ρ
  exact ((hs.pow 2).inv₀ (pow_ne_zero 2 h1)).add (continuousAt_const.mul (hs.inv₀ h1))

lemma qd_contAt {β ρ : ℝ} (hρ : ρ < 1) : ContinuousAt (qd β) ρ := by
  have h1 := one_sub_ne hρ
  have hs : ContinuousAt (fun x : ℝ => 1 - x) ρ := continuousAt_const.sub continuousAt_id
  show ContinuousAt (fun x => 2 * ((1 - x) ^ 3)⁻¹ + β * ((1 - x) ^ 2)⁻¹) ρ
  exact (continuousAt_const.mul ((hs.pow 3).inv₀ (pow_ne_zero 3 h1))).add
    (continuousAt_const.mul ((hs.pow 2).inv₀ (pow_ne_zero 2 h1)))

lemma rpow_contAt {β ρ : ℝ} (hβ : 1 ≤ β) : ContinuousAt (fun x : ℝ => x ^ (β - 1)) ρ :=
  (Real.continuous_rpow_const (by linarith)).continuousAt

lemma kf_contAt {C β ρ : ℝ} (hβ : 1 ≤ β) (hρ : ρ < 1) : ContinuousAt (kf C β) ρ := by
  show ContinuousAt (fun x => C * x ^ (β - 1) * x ^ 2 * qf β x) ρ
  exact ((continuousAt_const.mul (rpow_contAt hβ)).mul (continuousAt_id.pow 2)).mul (qf_contAt hρ)

lemma Gk_contAt {C β ρ : ℝ} (hβ : 1 ≤ β) (hρ : ρ < 1) : ContinuousAt (Gk C β) ρ := by
  have hB : ContinuousAt (Bq β) ρ := by
    show ContinuousAt (fun x => (β + 1) * qf β x + x * qd β x) ρ
    exact (continuousAt_const.mul (qf_contAt hρ)).add (continuousAt_id.mul (qd_contAt hρ))
  show ContinuousAt (fun x => C * x ^ (β - 1) * x ^ 2 * Bq β x) ρ
  exact ((continuousAt_const.mul (rpow_contAt hβ)).mul (continuousAt_id.pow 2)).mul hB

lemma sqrtk_contAt {C β ρ : ℝ} (hβ : 1 ≤ β) (hρ : ρ < 1) :
    ContinuousAt (fun x => Real.sqrt (1 - 4 * kf C β x)) ρ :=
  Real.continuous_sqrt.continuousAt.comp
    (continuousAt_const.sub (continuousAt_const.mul (kf_contAt hβ hρ)))

lemma phi_contAt {C β ρ : ℝ} (hβ : 1 ≤ β) (hρ : ρ < 1) : ContinuousAt (phi C β) ρ := by
  show ContinuousAt (fun x => x * (1 + Real.sqrt (1 - 4 * kf C β x))) ρ
  exact continuousAt_id.mul (continuousAt_const.add (sqrtk_contAt hβ hρ))

lemma psi_contAt {C β ρ : ℝ} (hβ : 1 ≤ β) (hρ : ρ < 1) : ContinuousAt (psi C β) ρ := by
  show ContinuousAt (fun x => Real.sqrt (1 - 4 * kf C β x) + (1 - 4 * kf C β x) - 2 * Gk C β x) ρ
  exact ((sqrtk_contAt hβ hρ).add (continuousAt_const.sub (continuousAt_const.mul
    (kf_contAt hβ hρ)))).sub (continuousAt_const.mul (Gk_contAt hβ hρ))

lemma hasDerivAt_qf {β x : ℝ} (hx : x < 1) : HasDerivAt (qf β) (qd β x) x := by
  have h1 := one_sub_ne hx
  have hs : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id' x).const_sub 1
  have e2 := (hs.pow 2).inv (pow_ne_zero 2 h1)
  have e1 := (hs.inv h1).const_mul β
  unfold qf
  refine (e2.add e1).congr_deriv ?_
  unfold qd
  try simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.inv_apply, Pi.sub_apply]
  field_simp
  ring

lemma hasDerivAt_kf {C β x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (kf C β) (kd C β x) x := by
  have hr := Real.hasDerivAt_rpow_const (p := β - 1) (Or.inl hx0.ne')
  have hp := hasDerivAt_pow 2 x
  have hq := hasDerivAt_qf (β := β) hx1
  unfold kf
  refine (((hr.const_mul C).mul hp).mul hq).congr_deriv ?_
  unfold kd
  rw [Real.rpow_sub_one hx0.ne' (β - 1)]
  try simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.inv_apply, Pi.sub_apply]
  field_simp
  ring

lemma phi_hasDeriv {C β x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hk : kf C β x < 1 / 4) :
    HasDerivAt (phi C β) (psi C β x / Real.sqrt (1 - 4 * kf C β x)) x := by
  have hpos : 0 < 1 - 4 * kf C β x := by linarith
  have hin : HasDerivAt (fun y => 1 - 4 * kf C β y) (-(4 * kd C β x)) x :=
    ((hasDerivAt_kf hx0 hx1).const_mul 4).const_sub 1
  have hsq := hin.sqrt hpos.ne'
  have hr : 0 < Real.sqrt (1 - 4 * kf C β x) := Real.sqrt_pos.2 hpos
  have hr2 : Real.sqrt (1 - 4 * kf C β x) ^ 2 = 1 - 4 * kf C β x := Real.sq_sqrt hpos.le
  have hG : Gk C β x = x * kd C β x := by unfold Gk kd Bq; ring
  unfold phi
  refine ((hasDerivAt_id' x).mul ((hasDerivAt_const x (1:ℝ)).add hsq)).congr_deriv ?_
  unfold psi
  rw [hG]
  try simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.inv_apply, Pi.sub_apply]
  beta_reduce
  generalize Real.sqrt (1 - 4 * kf C β x) = r at hr hr2 ⊢
  rw [← hr2]
  field_simp
  ring

lemma exists_rho_h {C β : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) :
    ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ kf C β ρ = 1 / 4 := by
  have hP : 0 < (1/2 : ℝ) ^ (β - 1) := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = C * (1/2 : ℝ) ^ (β - 1) / 4 := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; exact div_pos (mul_pos hC hP) (by norm_num)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (1/2 : ℝ) (2 * A) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1/2 := by rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ 2 * A := by rw [hδ]; exact min_le_right _ _
  have hb0 : (1:ℝ)/2 ≤ 1 - δ := by linarith
  have hb1 : 1 - δ < 1 := by linarith
  have hkb : 1/4 < kf C β (1 - δ) := by
    unfold kf
    have e1 : (1/2 : ℝ) ^ (β - 1) ≤ (1 - δ) ^ (β - 1) :=
      Real.rpow_le_rpow (by norm_num) hb0 (by linarith)
    have e2 : (1/4 : ℝ) ≤ (1 - δ) ^ 2 := by nlinarith
    have e3 : δ⁻¹ ≤ qf β (1 - δ) := by
      unfold qf
      rw [show (1:ℝ) - (1 - δ) = δ by ring]
      have : δ⁻¹ ≤ (δ ^ 2)⁻¹ := by
        apply inv_anti₀ (by positivity); nlinarith
      have : 0 ≤ β * δ⁻¹ := mul_nonneg (by linarith) (by positivity)
      linarith
    have e4 : (2 * A)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ0 hδ2
    have m1 : C * (1/2) ^ (β - 1) * (1/4) ≤ C * (1 - δ) ^ (β - 1) * (1 - δ) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left e1 hC.le) e2 (by norm_num)
        (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
    have m2 : C * (1/2) ^ (β - 1) * (1/4) * (2 * A)⁻¹ ≤
        C * (1 - δ) ^ (β - 1) * (1 - δ) ^ 2 * qf β (1 - δ) :=
      mul_le_mul m1 (e4.trans e3) (inv_nonneg.2 (by linarith))
        (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)) (sq_nonneg _))
    have m3 : C * (1/2) ^ (β - 1) * (1/4) * (2 * A)⁻¹ = 1/2 := by
      rw [hA]; field_simp
    linarith
  have hcont : ContinuousOn (kf C β) (Set.Icc 0 (1 - δ)) :=
    fun x hx => (kf_contAt hβ (by linarith [hx.2])).continuousWithinAt
  obtain ⟨ρ, hρ, hρe⟩ := intermediate_value_Icc (by linarith : (0:ℝ) ≤ 1 - δ) hcont
    (show (1/4 : ℝ) ∈ Set.Icc (kf C β 0) (kf C β (1 - δ)) from
      ⟨by rw [kf_zero]; norm_num, hkb.le⟩)
  refine ⟨ρ, ?_, by linarith [hρ.2], hρe⟩
  rcases eq_or_lt_of_le hρ.1 with h | h
  · rw [← h, kf_zero] at hρe; norm_num at hρe
  · exact h

lemma psi_anti {C β a b : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (ha : 0 ≤ a) (hab : a < b) (hb1 : b < 1) :
    psi C β b < psi C β a := by
  unfold psi
  have k1 := kf_lt hC hβ ha hab hb1
  have g1 := Gk_lt hC hβ ha hab hb1
  have s1 : Real.sqrt (1 - 4 * kf C β b) ≤ Real.sqrt (1 - 4 * kf C β a) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

lemma phi_shape {C β : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) {ρh : ℝ} (hh0 : 0 < ρh) (hh1 : ρh < 1)
    (hkh : kf C β ρh = 1 / 4) :
    ∃ ρ2, 0 < ρ2 ∧ ρ2 < ρh ∧ StrictMonoOn (phi C β) (Set.Icc 0 ρ2) ∧
      StrictAntiOn (phi C β) (Set.Icc ρ2 ρh) := by
  have hpsi0 : psi C β 0 = 2 := by unfold psi; rw [kf_zero, Gk_zero]; norm_num
  have hpsih : psi C β ρh < 0 := by
    unfold psi
    rw [hkh, show (1:ℝ) - 4 * (1/4) = 0 by norm_num, Real.sqrt_zero]
    have := Gk_lt hC hβ le_rfl hh0 hh1
    rw [Gk_zero] at this
    linarith
  obtain ⟨ρ2, hρ2, hψ⟩ := intermediate_value_Icc' hh0.le
    (fun x hx => (psi_contAt (C := C) hβ (by linarith [hx.2])).continuousWithinAt)
    (show (0:ℝ) ∈ Set.Icc (psi C β ρh) (psi C β 0) from ⟨hpsih.le, by rw [hpsi0]; norm_num⟩)
  have h20 : 0 < ρ2 := by
    rcases eq_or_lt_of_le hρ2.1 with h | h
    · rw [← h, hpsi0] at hψ; norm_num at hψ
    · exact h
  have h2h : ρ2 < ρh := by
    rcases eq_or_lt_of_le hρ2.2 with h | h
    · rw [h] at hψ; linarith
    · exact h
  have kless : ∀ x, 0 ≤ x → x < ρh → kf C β x < 1 / 4 := by
    intro x hx0 hx; rw [← hkh]; exact kf_lt hC hβ hx0 hx hh1
  refine ⟨ρ2, h20, h2h, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Icc 0 ρ2)
    · exact fun x hx => (phi_contAt (C := C) hβ (by linarith [hx.2])).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hk := kless x hx.1.le (by linarith [hx.2])
      rw [(phi_hasDeriv hx.1 (by linarith [hx.2]) hk).deriv]
      have hp : 0 < psi C β x := by
        have := psi_anti hC hβ hx.1.le hx.2 (by linarith); linarith
      exact div_pos hp (Real.sqrt_pos.2 (by linarith))
  · apply strictAntiOn_of_deriv_neg (convex_Icc ρ2 ρh)
    · exact fun x hx => (phi_contAt (C := C) hβ (by linarith [hx.2])).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hk := kless x hx0.le hx.2
      rw [(phi_hasDeriv hx0 (by linarith [hx.2]) hk).deriv]
      have hp : psi C β x < 0 := by
        have := psi_anti hC hβ h20.le hx.1 (by linarith [hx.2]); linarith
      exact div_neg_of_neg_of_pos hp (Real.sqrt_pos.2 (by linarith))

lemma phi_eq {C β s ρ : ℝ} (p : CP C β s ρ) (hs : 1 / 2 ≤ s) : ρ * s = phi C β ρ / 2 := by
  unfold phi
  have h : Real.sqrt (1 - 4 * kf C β ρ) = 2 * s - 1 := by
    rw [← p.eq, show 1 - 4 * (s * (1 - s)) = (2 * s - 1) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  rw [h]; ring

lemma m_le (s : ℝ) : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1/2)]

lemma assemble {C β K L : ℝ} (hC : 0 < C) (hβ : 1 ≤ β) (hK : 0 < K) (sN ρN : ℝ → ℝ)
    (hcp : ∀ N, L < N → CP C β (sN N) (ρN N))
    (hNN : ∀ N, L < N → N = Nf K (sN N) (ρN N))
    (hlow : ∀ s ρ, CP C β s ρ → L < Nf K s ρ) :
    StrictAntiOn sN (Set.Ioi L) ∧
    (∃ N₀, 0 < N₀ ∧ L < N₀ ∧ StrictMonoOn ρN (Set.Ioo L N₀) ∧ StrictAntiOn ρN (Set.Ioi N₀)) ∧
    (∃ N₀, 0 < N₀ ∧ L < N₀ ∧ StrictMonoOn (fun N => ρN N * sN N) (Set.Ioo L N₀) ∧
        StrictAntiOn (fun N => ρN N * sN N) (Set.Ioi N₀)) := by
  have lt_pt : ∀ N, L < N → ∀ s ρ, CP C β s ρ → N < Nf K s ρ → s < sN N := by
    intro N hN s ρ p h
    exact cmp hC hβ hK (hcp N hN) p (by rw [← hNN N hN]; exact h)
  have pt_lt : ∀ N, L < N → ∀ s ρ, CP C β s ρ → Nf K s ρ < N → sN N < s := by
    intro N hN s ρ p h
    exact cmp hC hβ hK p (hcp N hN) (by rw [← hNN N hN]; exact h)
  have anti : StrictAntiOn sN (Set.Ioi L) := by
    intro a ha b hb hab
    exact lt_pt a ha (sN b) (ρN b) (hcp b hb) (by rw [← hNN b hb]; exact hab)
  have rlt : ∀ a b, L < a → L < b → kf C β (ρN a) < kf C β (ρN b) → ρN a < ρN b := by
    intro a b ha hb h
    exact (kf_lt_iff hC hβ (hcp a ha).r0.le (hcp a ha).r1 (hcp b hb).r0.le (hcp b hb).r1).1 h
  obtain ⟨ρh, hh0, hh1, hkh⟩ := exists_rho_h hC hβ
  have ph : CP C β (1/2) ρh := ⟨by norm_num, by norm_num, hh0, hh1, by rw [hkh]; norm_num⟩
  -- points with kf ≤ 1/4 lie below ρh
  have le_h : ∀ N, L < N → ρN N ≤ ρh := by
    intro N hN
    by_contra hc; push Not at hc
    have := kf_lt hC hβ hh0.le hc (hcp N hN).r1
    have := m_le (sN N)
    rw [(hcp N hN).eq, hkh] at *
    linarith
  refine ⟨anti, ⟨Nf K (1/2) ρh, Nf_pos hK ph, hlow _ _ ph, ?_, ?_⟩, ?_⟩
  · intro a ha b hb hab
    have pa := hcp a ha.1
    have pb := hcp b hb.1
    have hs : sN b < sN a := anti ha.1 hb.1 hab
    have hb2 : 1/2 < sN b := lt_pt b hb.1 _ _ ph hb.2
    apply rlt a b ha.1 hb.1
    rw [← pa.eq, ← pb.eq]; nlinarith
  · intro a ha b hb hab
    have ha' : L < a := lt_trans (hlow _ _ ph) ha
    have hb' : L < b := lt_trans (hlow _ _ ph) hb
    have pa := hcp a ha'
    have pb := hcp b hb'
    have hs : sN b < sN a := anti ha' hb' hab
    have ha2 : sN a < 1/2 := pt_lt a ha' _ _ ph ha
    apply rlt b a hb' ha'
    rw [← pa.eq, ← pb.eq]; nlinarith
  · obtain ⟨ρ2, h20, h2h, hmono, hanti⟩ := phi_shape hC hβ hh0 hh1 hkh
    have hk2 : kf C β ρ2 < 1/4 := by rw [← hkh]; exact kf_lt hC hβ h20.le h2h hh1
    have hk20 : 0 < kf C β ρ2 := kf_pos hC hβ h20 (by linarith)
    obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (1 - 4 * kf C β ρ2) := ⟨_, rfl⟩
    have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 (by linarith)
    have hr2 : r ^ 2 = 1 - 4 * kf C β ρ2 := by rw [hr]; exact Real.sq_sqrt (by linarith)
    have hr1 : r < 1 := by nlinarith
    have p2 : CP C β ((1 + r) / 2) ρ2 :=
      ⟨by linarith, by linarith, h20, by linarith, by linear_combination (-1/4 : ℝ) * hr2⟩
    have hs2 : 1/2 < (1 + r) / 2 := by linarith
    have hphih : phi C β ρh = ρh := by
      unfold phi; rw [hkh, show (1:ℝ) - 4 * (1/4) = 0 by norm_num, Real.sqrt_zero]; ring
    refine ⟨Nf K ((1 + r) / 2) ρ2, Nf_pos hK p2, hlow _ _ p2, ?_, ?_⟩
    · intro a ha b hb hab
      have pa := hcp a ha.1
      have pb := hcp b hb.1
      have hs : sN b < sN a := anti ha.1 hb.1 hab
      have hb2 : (1 + r) / 2 < sN b := lt_pt b hb.1 _ _ p2 hb.2
      have hab' : ρN a < ρN b := by
        apply rlt a b ha.1 hb.1
        rw [← pa.eq, ← pb.eq]; nlinarith
      have hb3 : ρN b < ρ2 := by
        have : kf C β (ρN b) < kf C β ρ2 := by rw [← pb.eq, ← p2.eq]; nlinarith
        exact (kf_lt_iff hC hβ pb.r0.le pb.r1 h20.le (by linarith)).1 this
      show ρN a * sN a < ρN b * sN b
      rw [phi_eq pa (by linarith), phi_eq pb (by linarith)]
      have := hmono ⟨pa.r0.le, by linarith⟩ ⟨pb.r0.le, hb3.le⟩ hab'
      linarith
    · intro a ha b hb hab
      have ha' : L < a := lt_trans (hlow _ _ p2) ha
      have hb' : L < b := lt_trans (hlow _ _ p2) hb
      have pa := hcp a ha'
      have pb := hcp b hb'
      have hs : sN b < sN a := anti ha' hb' hab
      have ha2 : sN a < (1 + r) / 2 := pt_lt a ha' _ _ p2 ha
      show ρN b * sN b < ρN a * sN a
      rcases le_or_gt (1/2) (sN b) with hb2 | hb2
      · have h2a : ρ2 < ρN a := by
          have : kf C β ρ2 < kf C β (ρN a) := by rw [← pa.eq, ← p2.eq]; nlinarith
          exact (kf_lt_iff hC hβ h20.le (by linarith) pa.r0.le pa.r1).1 this
        have hab' : ρN a < ρN b := by
          apply rlt a b ha' hb'
          rw [← pa.eq, ← pb.eq]; nlinarith
        rw [phi_eq pa (by linarith), phi_eq pb hb2]
        have := hanti ⟨h2a.le, le_h a ha'⟩ ⟨by linarith, le_h b hb'⟩ hab'
        linarith
      · rcases le_or_gt (sN a) (1/2) with ha3 | ha3
        · have hba : ρN b < ρN a := by
            apply rlt b a hb' ha'
            rw [← pa.eq, ← pb.eq]; nlinarith
          exact mul_lt_mul'' hba hs pb.r0.le pb.s0.le
        · have h2a : ρ2 < ρN a := by
            have : kf C β ρ2 < kf C β (ρN a) := by rw [← pa.eq, ← p2.eq]; nlinarith
            exact (kf_lt_iff hC hβ h20.le (by linarith) pa.r0.le pa.r1).1 this
          have hah : ρN a < ρh := by
            have : kf C β (ρN a) < kf C β ρh := by rw [← pa.eq, hkh]; nlinarith
            exact (kf_lt_iff hC hβ pa.r0.le pa.r1 hh0.le hh1).1 this
          have hbh : ρN b < ρh := by
            have : kf C β (ρN b) < kf C β ρh := by rw [← pb.eq, hkh]; nlinarith
            exact (kf_lt_iff hC hβ pb.r0.le pb.r1 hh0.le hh1).1 this
          have h1 := hanti ⟨h2a.le, hah.le⟩ ⟨h2h.le, le_rfl⟩ hah
          have h3 : ρN b * sN b < ρh * (1/2) := mul_lt_mul'' hbh hb2 pb.r0.le pb.s0.le
          rw [phi_eq pa ha3.le]
          linarith

/-! ## Part B: the model. -/

open LaborWelfare.PoolSize MeasureTheory Filter Topology

lemma Einv_pos (M : Model) (hM : M.Std) : 0 < Einv M := by
  obtain ⟨-, -, -, -, hP, halo, hle, hsupp⟩ := hM
  haveI := hP
  have hae : ∀ᵐ a ∂M.F, a ∈ Set.Icc M.alo M.ahi := ae_iff.2 hsupp
  have hint : Integrable (fun a : ℝ => a⁻¹) M.F := by
    refine Integrable.mono' (integrable_const (M.alo⁻¹)) measurable_inv.aestronglyMeasurable ?_
    filter_upwards [hae] with a ha
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith [ha.1])]
    exact inv_anti₀ halo ha.1
  have h1 : ∫ _a, M.ahi⁻¹ ∂M.F ≤ ∫ a, a⁻¹ ∂M.F :=
    integral_mono_ae (integrable_const _) hint
      (by filter_upwards [hae] with a ha; exact inv_anti₀ (by linarith [ha.1]) ha.2)
  have h2 : ∫ _a, M.ahi⁻¹ ∂M.F = M.ahi⁻¹ := by simp
  have h3 : 0 < M.ahi⁻¹ := inv_pos.2 (by linarith)
  unfold Einv
  linarith

lemma avgLW_eq (M : Model) {N : ℝ} (hN : N ≠ 0) (o : Outcome) :
    avgLaborWelfare M N o = effWage o ^ 2 * Einv M / 4 := by
  unfold avgLaborWelfare laborWelfare Einv
  have : ∀ a : ℝ, effWage o * xstar o.w o.D o.S a - a * (xstar o.w o.D o.S a) ^ 2
      = (effWage o ^ 2 / 4) * a⁻¹ := by
    intro a
    unfold xstar effWage
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rcases eq_or_ne o.S 0 with hS | hS
      · simp [hS]
      · field_simp; ring
  simp_rw [this, integral_const_mul]
  field_simp

lemma Nlow_nonneg (M : Model) (hv : 0 < M.vbar) (hh : 0 ≤ M.h) (hE : 0 < Einv M) :
    0 ≤ Nlow M := by
  unfold Nlow
  split_ifs
  · exact div_nonneg (by linarith) (mul_pos (pow_pos hv 2) hE).le
  · exact le_rfl

lemma G_eq (M : Model) (hv : 0 < M.vbar) {x : ℝ} (hx : 0 ≤ x)
    (hD : 0 < M.Lam * (1 - G M x)) : G M x = x / M.vbar ∧ x < M.vbar := by
  unfold G at *
  have hx' : 0 ≤ x / M.vbar := div_nonneg hx hv.le
  by_cases h1 : x / M.vbar < 1
  · rw [min_eq_right h1.le, max_eq_right hx']
    exact ⟨rfl, (div_lt_one hv).1 h1⟩
  · push Not at h1
    rw [min_eq_left h1, max_eq_right zero_le_one] at hD
    simp at hD

lemma hdelay_nonneg (M : Model) (hh : 0 ≤ M.h) {D S : ℝ} (hD : 0 < D) (hS : 0 < S)
    (hDS : M.h ≠ 0 → D < S) : 0 ≤ M.h * delay M D S := by
  rcases eq_or_ne M.h 0 with h0 | h0
  · simp [h0]
  · apply mul_nonneg hh
    unfold delay
    have := hDS h0
    exact div_nonneg (Real.rpow_nonneg (div_nonneg hD.le hS.le) _) (by linarith)

lemma feas_dest (M : Model) (hM : M.Std) {N : ℝ} (hN : 0 < N) {o : Outcome}
    (hf : IsFeasible M N o) :
    0 < o.D ∧ 0 < o.S ∧ o.D ≤ o.S ∧ (M.h ≠ 0 → o.D < o.S) ∧
      o.w = 2 * o.S ^ 2 / (o.D * N * Einv M) ∧ o.p = priceDS M o.D o.S ∧
      profit o = PiDS M N o.D o.S := by
  have hE := Einv_pos M hM
  obtain ⟨hv, hL, hh, -, -, -, -, -⟩ := hM
  obtain ⟨hp, -, hD, hS, hDS, hSeq, hDeq⟩ := hf
  have hDS' : o.D ≤ o.S ∧ (M.h ≠ 0 → o.D < o.S) := by
    split_ifs at hDS with h0
    · exact ⟨hDS, fun h => absurd h0 h⟩
    · exact ⟨hDS.le, fun _ => hDS⟩
  have hdel := hdelay_nonneg M hh hD hS hDS'.2
  have hG := G_eq M hv (add_nonneg hp hdel) (by rw [← hDeq]; exact hD)
  have hv0 : M.vbar ≠ 0 := hv.ne'
  have hL0 : M.Lam ≠ 0 := hL.ne'
  have hpr : o.p = priceDS M o.D o.S := by
    unfold priceDS
    have h2 := hDeq
    rw [hG.1] at h2
    generalize M.h * delay M o.D o.S = X at h2 ⊢
    have e : M.vbar * o.D / M.Lam = M.vbar - (o.p + X) := by
      rw [h2]; field_simp
    linarith
  have hpos : 0 < o.w * o.D * N * Einv M / 2 := Real.sqrt_pos.1 (by rw [← hSeq]; exact hS)
  have hS2 : o.S ^ 2 = o.w * o.D * N * Einv M / 2 := by rw [hSeq, Real.sq_sqrt hpos.le]
  have hw : o.w = 2 * o.S ^ 2 / (o.D * N * Einv M) := by
    rw [hS2]; field_simp
  refine ⟨hD, hS, hDS'.1, hDS'.2, hw, hpr, ?_⟩
  unfold profit PiDS
  rw [← hpr, hw]
  field_simp

lemma feas_mk (M : Model) (hM : M.Std) {N D S : ℝ} (hN : 0 < N) (hD : 0 < D) (hDS : D ≤ S)
    (hDS' : M.h ≠ 0 → D < S) (hpos : 0 < PiDS M N D S) :
    IsFeasible M N ⟨priceDS M D S, 2 * S ^ 2 / (D * N * Einv M), D, S⟩ ∧
      profit ⟨priceDS M D S, 2 * S ^ 2 / (D * N * Einv M), D, S⟩ = PiDS M N D S := by
  have hE := Einv_pos M hM
  obtain ⟨hv, hL, hh, -, -, -, -, -⟩ := hM
  have hS : 0 < S := lt_of_lt_of_le hD hDS
  have hv0 : M.vbar ≠ 0 := hv.ne'
  have hL0 : M.Lam ≠ 0 := hL.ne'
  have hE0 : Einv M ≠ 0 := hE.ne'
  have hprof : profit ⟨priceDS M D S, 2 * S ^ 2 / (D * N * Einv M), D, S⟩ = PiDS M N D S := by
    unfold profit PiDS
    field_simp
  refine ⟨⟨?_, ?_, hD, hS, ?_, ?_, ?_⟩, hprof⟩
  · have h1 : 0 ≤ 2 * S ^ 2 / (N * Einv M) :=
      div_nonneg (by positivity) (mul_pos hN hE).le
    have h2 : 0 < priceDS M D S * D := by unfold PiDS at hpos; linarith
    by_contra hc; push Not at hc
    nlinarith
  · exact div_nonneg (by positivity) (mul_pos (mul_pos hD hN) hE).le
  · split_ifs with h0
    · exact hDS
    · exact hDS' h0
  · show S = Real.sqrt (2 * S ^ 2 / (D * N * Einv M) * D * N * Einv M / 2)
    rw [show 2 * S ^ 2 / (D * N * Einv M) * D * N * Einv M / 2 = S ^ 2 by
      field_simp, Real.sqrt_sq hS.le]
  · show D = M.Lam * (1 - G M (priceDS M D S + M.h * delay M D S))
    have hx : priceDS M D S + M.h * delay M D S = M.vbar - M.vbar * D / M.Lam := by
      unfold priceDS; ring
    have hdel := hdelay_nonneg M hh hD hS hDS'
    have hp0 : 0 < priceDS M D S := by
      have h1 : 0 ≤ 2 * S ^ 2 / (N * Einv M) :=
        div_nonneg (by positivity) (mul_pos hN hE).le
      have h2 : 0 < priceDS M D S * D := by unfold PiDS at hpos; linarith
      by_contra hc; push Not at hc
      nlinarith
    have hxpos : 0 ≤ M.vbar - M.vbar * D / M.Lam := by rw [← hx]; linarith
    have hDL : 0 < M.vbar * D / M.Lam := div_pos (mul_pos hv hD) hL
    rw [hx]
    unfold G
    have e1 : (M.vbar - M.vbar * D / M.Lam) / M.vbar = 1 - D / M.Lam := by
      field_simp
    have e2 : 0 ≤ 1 - D / M.Lam := by rw [← e1]; exact div_nonneg hxpos hv.le
    have e3 : 1 - D / M.Lam < 1 := by
      have : 0 < D / M.Lam := div_pos hD hL
      linarith
    rw [e1, min_eq_right e3.le, max_eq_right e2]
    field_simp
    ring

noncomputable def Qf (v L h β c ρ : ℝ) : ℝ :=
  v ^ 2 * ρ ^ 2 / (4 * (v * ρ ^ 2 / L + c)) - h * (ρ ^ (β - 1) * ρ ^ 2 / (1 - ρ))
noncomputable def Qd (v L h β c ρ : ℝ) : ℝ :=
  v ^ 2 * ρ * c / (2 * (v * ρ ^ 2 / L + c) ^ 2) - h * (ρ ^ (β - 1) * ρ * qf β ρ)
noncomputable def Bf (v L h β c ρ : ℝ) : ℝ :=
  v ^ 2 / (4 * (v * ρ ^ 2 / L + c)) - h * (ρ ^ (β - 1) / (1 - ρ))

lemma hasDerivAt_Qf {v L h β c ρ : ℝ} (hv : 0 < v) (hL : 0 < L) (hc : 0 < c) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) : HasDerivAt (Qf v L h β c) (Qd v L h β c ρ) ρ := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := one_sub_ne hρ1
  have ha : 0 < v * ρ ^ 2 / L + c := by
    have := div_pos (mul_pos hv (pow_pos hρ0 2)) hL; linarith
  have hden : 4 * (v * ρ ^ 2 / L + c) ≠ 0 := by positivity
  have hn := (hasDerivAt_pow 2 ρ).const_mul (v ^ 2)
  have hd := ((((hasDerivAt_pow 2 ρ).const_mul v).div_const L).add_const c).const_mul 4
  have hr := Real.hasDerivAt_rpow_const (p := β - 1) (Or.inl hρ0.ne')
  have hs : HasDerivAt (fun x : ℝ => 1 - x) (-1) ρ := (hasDerivAt_id' ρ).const_sub 1
  have hg := ((hr.mul (hasDerivAt_pow 2 ρ)).div hs h1).const_mul h
  unfold Qf
  refine ((hn.div hd hden).sub hg).congr_deriv ?_
  unfold Qd qf
  rw [Real.rpow_sub_one hρ0.ne' (β - 1)]
  try simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.inv_apply, Pi.sub_apply]
  have hL0 : L ≠ 0 := hL.ne'
  have hρ0' : ρ ≠ 0 := hρ0.ne'
  have ha' : v * ρ ^ 2 + c * L ≠ 0 := by
    have := mul_pos hc hL; have := mul_pos hv (pow_pos hρ0 2); positivity
  field_simp
  ring

lemma PiDS_rho (M : Model) {N c ρ S : ℝ} (hc : c = 2 / (N * Einv M)) (hN : 0 < N)
    (hE : 0 < Einv M) (hL : 0 < M.Lam) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hS : 0 < S) :
    PiDS M N (ρ * S) S = M.vbar * ρ * S - (M.vbar * ρ ^ 2 / M.Lam + c) * S ^ 2
      - M.h * (ρ ^ (M.beta - 1) * ρ ^ 2 / (1 - ρ)) := by
  unfold PiDS priceDS delay
  rw [mul_div_cancel_right₀ ρ hS.ne']
  have hb : ρ ^ M.beta = ρ ^ (M.beta - 1) * ρ := by
    rw [Real.rpow_sub_one hρ0.ne', div_mul_cancel₀ _ hρ0.ne']
  rw [hb, hc]
  have h1 : S - ρ * S ≠ 0 := by
    have : 0 < S - ρ * S := by nlinarith
    exact this.ne'
  have h2 : (1:ℝ) - ρ ≠ 0 := one_sub_ne hρ1
  have hL0 : M.Lam ≠ 0 := hL.ne'
  have hN0 : N ≠ 0 := hN.ne'
  have hE0 : Einv M ≠ 0 := hE.ne'
  have hS0 : S ≠ 0 := hS.ne'
  field_simp
  ring

lemma PiDS_Q (M : Model) {N c ρ S : ℝ} (hc : c = 2 / (N * Einv M)) (hN : 0 < N)
    (hE : 0 < Einv M) (hv : 0 < M.vbar) (hL : 0 < M.Lam) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hS : 0 < S) :
    PiDS M N (ρ * S) S = Qf M.vbar M.Lam M.h M.beta c ρ -
      (M.vbar * ρ ^ 2 / M.Lam + c) *
        (S - M.vbar * ρ / (2 * (M.vbar * ρ ^ 2 / M.Lam + c))) ^ 2 := by
  have hc0 : 0 < c := by rw [hc]; exact div_pos two_pos (mul_pos hN hE)
  rw [PiDS_rho M hc hN hE hL hρ0 hρ1 hS]
  unfold Qf
  have ha : 0 < M.vbar * ρ ^ 2 / M.Lam + c := by
    have := div_pos (mul_pos hv (pow_pos hρ0 2)) hL; linarith
  generalize M.vbar * ρ ^ 2 / M.Lam + c = a at ha ⊢
  have ha0 : a ≠ 0 := ha.ne'
  field_simp
  ring

lemma exists_Qpos (M : Model) (hv : 0 < M.vbar) (hL : 0 < M.Lam) (hh : 0 ≤ M.h)
    (hβ : 1 ≤ M.beta) (hE : 0 < Einv M) {N c : ℝ} (hNl : Nlow M < N) (hN : 0 < N)
    (hc : c = 2 / (N * Einv M)) :
    ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ 0 < Qf M.vbar M.Lam M.h M.beta c ρ := by
  have hc0 : 0 < c := by rw [hc]; exact div_pos two_pos (mul_pos hN hE)
  have hQB : ∀ ρ, Qf M.vbar M.Lam M.h M.beta c ρ = ρ ^ 2 * Bf M.vbar M.Lam M.h M.beta c ρ := by
    intro ρ; unfold Qf Bf; ring
  have hB0e : Bf M.vbar M.Lam M.h M.beta c 0 = M.vbar ^ 2 / (4 * c) - M.h * (0:ℝ) ^ (M.beta - 1) := by
    unfold Bf; ring
  have hB0 : 0 < Bf M.vbar M.Lam M.h M.beta c 0 := by
    rw [hB0e]
    rcases eq_or_lt_of_le hβ with hb1 | hb1
    · have hNl' := hNl
      unfold Nlow at hNl'
      rw [if_pos hb1.symm] at hNl'
      rw [← hb1, sub_self, Real.rpow_zero, mul_one]
      rw [div_lt_iff₀ (mul_pos (pow_pos hv 2) hE)] at hNl'
      rw [hc]
      have hE0 : Einv M ≠ 0 := hE.ne'
      have hN0 : N ≠ 0 := hN.ne'
      have e : M.vbar ^ 2 / (4 * (2 / (N * Einv M))) - M.h = (N * (M.vbar ^ 2 * Einv M) - 8 * M.h) / 8 := by
        field_simp; ring
      rw [e]
      linarith
    · rw [Real.zero_rpow (by linarith), mul_zero, sub_zero]
      exact div_pos (pow_pos hv 2) (by linarith)
  have hBc : ContinuousAt (Bf M.vbar M.Lam M.h M.beta c) 0 := by
    have hden : ContinuousAt (fun ρ : ℝ => 4 * (M.vbar * ρ ^ 2 / M.Lam + c)) 0 := by fun_prop
    have h1 : ContinuousAt (fun ρ : ℝ => M.vbar ^ 2 / (4 * (M.vbar * ρ ^ 2 / M.Lam + c))) 0 :=
      continuousAt_const.div hden (show (4:ℝ) * (M.vbar * 0 ^ 2 / M.Lam + c) ≠ 0 by
      rw [show (4:ℝ) * (M.vbar * 0 ^ 2 / M.Lam + c) = 4 * c by ring]; positivity)
    have h2 : ContinuousAt (fun ρ : ℝ => ρ ^ (M.beta - 1) / (1 - ρ)) 0 :=
      (rpow_contAt hβ).div (continuousAt_const.sub continuousAt_id) (by norm_num)
    show ContinuousAt (fun ρ => M.vbar ^ 2 / (4 * (M.vbar * ρ ^ 2 / M.Lam + c)) -
      M.h * (ρ ^ (M.beta - 1) / (1 - ρ))) 0
    exact h1.sub (continuousAt_const.mul h2)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hBc.tendsto.eventually (lt_mem_nhds hB0))
  have hm0 : 0 < min (ε / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have hm1 : min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
  have hm2 : min (ε / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  refine ⟨min (ε / 2) (1 / 2), hm0, by linarith, ?_⟩
  rw [hQB]
  apply mul_pos (by positivity)
  apply hball
  rw [Real.dist_eq, sub_zero, abs_of_pos hm0]
  linarith

lemma char_pos (M : Model) (hM : M.Std) (hpos : 0 < M.h) {N : ℝ} (hNl : Nlow M < N)
    {o : Outcome} (ho : IsOptimal M N o) :
    CP (2 * M.h / (M.vbar * M.Lam)) M.beta (2 * o.w / M.vbar) (util o) ∧
      N = Nf (2 * M.Lam / (Einv M * M.vbar)) (2 * o.w / M.vbar) (util o) := by
  have hE := Einv_pos M hM
  have hM' := hM
  obtain ⟨hv, hL, hh, hβ, -, -, -, -⟩ := hM
  have hN : 0 < N := lt_of_le_of_lt (Nlow_nonneg M hv hh hE) hNl
  obtain ⟨c, hc⟩ : ∃ c, c = 2 / (N * Einv M) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact div_pos two_pos (mul_pos hN hE)
  obtain ⟨hfeas, hmax⟩ := ho
  obtain ⟨hD, hS, -, hDS, hw, -, hprof⟩ := feas_dest M hM' hN hfeas
  have hDS' := hDS hpos.ne'
  have hρ0 : 0 < util o := div_pos hD hS
  have hρ1 : util o < 1 := (div_lt_one hS).2 hDS'
  have hDρ : o.D = util o * o.S := by unfold util; field_simp
  generalize util o = ρ at hρ0 hρ1 hDρ ⊢
  have hcmp : ∀ ρ', 0 < ρ' → ρ' < 1 → 0 < Qf M.vbar M.Lam M.h M.beta c ρ' →
      Qf M.vbar M.Lam M.h M.beta c ρ' ≤ profit o := by
    intro ρ' h0 h1 hQ
    have ha : 0 < M.vbar * ρ' ^ 2 / M.Lam + c := by
      have := div_pos (mul_pos hv (pow_pos h0 2)) hL; linarith
    obtain ⟨S', hS'⟩ : ∃ S', S' = M.vbar * ρ' / (2 * (M.vbar * ρ' ^ 2 / M.Lam + c)) := ⟨_, rfl⟩
    have hS'0 : 0 < S' := by rw [hS']; exact div_pos (mul_pos hv h0) (by linarith)
    have hPi : PiDS M N (ρ' * S') S' = Qf M.vbar M.Lam M.h M.beta c ρ' := by
      rw [PiDS_Q M hc hN hE hv hL h0 h1 hS'0, ← hS']; simp
    obtain ⟨hf', hp'⟩ := feas_mk M hM' hN (D := ρ' * S') (S := S') (mul_pos h0 hS'0)
      (by nlinarith) (fun _ => by nlinarith) (by rw [hPi]; exact hQ)
    have := hmax _ hf'
    rw [hp', hPi] at this
    exact this
  obtain ⟨ρ0, h00, h01, hQ0⟩ := exists_Qpos M hv hL hh hβ hE hNl hN hc
  have hprof_pos : 0 < profit o := lt_of_lt_of_le hQ0 (hcmp ρ0 h00 h01 hQ0)
  have ha : 0 < M.vbar * ρ ^ 2 / M.Lam + c := by
    have := div_pos (mul_pos hv (pow_pos hρ0 2)) hL; linarith
  have hprofQ : profit o = Qf M.vbar M.Lam M.h M.beta c ρ - (M.vbar * ρ ^ 2 / M.Lam + c) *
      (o.S - M.vbar * ρ / (2 * (M.vbar * ρ ^ 2 / M.Lam + c))) ^ 2 := by
    rw [hprof, hDρ, PiDS_Q M hc hN hE hv hL hρ0 hρ1 hS]
  have hnn : 0 ≤ (M.vbar * ρ ^ 2 / M.Lam + c) *
      (o.S - M.vbar * ρ / (2 * (M.vbar * ρ ^ 2 / M.Lam + c))) ^ 2 :=
    mul_nonneg ha.le (sq_nonneg _)
  have hQρ : 0 < Qf M.vbar M.Lam M.h M.beta c ρ := by linarith
  have hle := hcmp ρ hρ0 hρ1 hQρ
  have hzero : (M.vbar * ρ ^ 2 / M.Lam + c) *
      (o.S - M.vbar * ρ / (2 * (M.vbar * ρ ^ 2 / M.Lam + c))) ^ 2 = 0 := by linarith
  have hSopt : o.S = M.vbar * ρ / (2 * (M.vbar * ρ ^ 2 / M.Lam + c)) := by
    have := (mul_eq_zero.1 hzero).resolve_left ha.ne'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  have hderiv := hasDerivAt_Qf (h := M.h) (β := M.beta) hv hL hc0 hρ0 hρ1
  have hlocmax : IsLocalMax (Qf M.vbar M.Lam M.h M.beta c) ρ := by
    have hev1 : ∀ᶠ x in 𝓝 ρ, 0 < Qf M.vbar M.Lam M.h M.beta c x :=
      hderiv.continuousAt.tendsto.eventually (lt_mem_nhds hQρ)
    have hev2 : Set.Ioo (0:ℝ) 1 ∈ 𝓝 ρ := Ioo_mem_nhds hρ0 hρ1
    filter_upwards [hev1, hev2] with x hx1 hx2
    have := hcmp x hx2.1 hx2.2 hx1
    linarith
  have hfoc := hlocmax.hasDerivAt_eq_zero hderiv
  unfold Qd at hfoc
  -- the wage
  have hv0 : M.vbar ≠ 0 := hv.ne'
  have hL0 : M.Lam ≠ 0 := hL.ne'
  have hs_eq : 2 * o.w / M.vbar = c / (M.vbar * ρ ^ 2 / M.Lam + c) := by
    rw [hw, hDρ, hSopt, hc]
    have hN0 : N ≠ 0 := hN.ne'
    have hE0 : Einv M ≠ 0 := hE.ne'
    have hρ0' : ρ ≠ 0 := hρ0.ne'
    have ha0 : M.vbar * ρ ^ 2 / M.Lam + 2 / (N * Einv M) ≠ 0 := by rw [← hc]; exact ha.ne'
    field_simp
  rw [hs_eq]
  have hvr : 0 < M.vbar * ρ ^ 2 / M.Lam := div_pos (mul_pos hv (pow_pos hρ0 2)) hL
  refine ⟨⟨div_pos hc0 ha, (div_lt_one ha).2 (by linarith), hρ0, hρ1, ?_⟩, ?_⟩
  · unfold kf
    have e1 : M.h * (ρ ^ (M.beta - 1) * ρ * qf M.beta ρ) =
        M.vbar ^ 2 * ρ * c / (2 * (M.vbar * ρ ^ 2 / M.Lam + c) ^ 2) := by linarith
    have e2 : 2 * M.h / (M.vbar * M.Lam) * ρ ^ (M.beta - 1) * ρ ^ 2 * qf M.beta ρ =
        2 / (M.vbar * M.Lam) * ρ * (M.h * (ρ ^ (M.beta - 1) * ρ * qf M.beta ρ)) := by ring
    rw [e2, e1]
    generalize ha_eq : M.vbar * ρ ^ 2 / M.Lam + c = a at ha hvr ⊢
    have ha0 : a ≠ 0 := ha.ne'
    field_simp
    ring_nf
    rw [← ha_eq]
    field_simp
    ring
  · unfold Nf
    have e : 1 - c / (M.vbar * ρ ^ 2 / M.Lam + c) =
        M.vbar * ρ ^ 2 / M.Lam / (M.vbar * ρ ^ 2 / M.Lam + c) := by
      field_simp; ring
    rw [e]
    generalize M.vbar * ρ ^ 2 / M.Lam + c = a at ha hvr ⊢
    have ha0 : a ≠ 0 := ha.ne'
    have hρ0' : ρ ≠ 0 := hρ0.ne'
    have hN0 : N ≠ 0 := hN.ne'
    have hE0 : Einv M ≠ 0 := hE.ne'
    rw [hc]
    field_simp

lemma h0_char (M : Model) (hM : M.Std) (h0 : M.h = 0) {N : ℝ} (hN : 0 < N) {o : Outcome}
    (ho : IsOptimal M N o) :
    o.w = M.vbar * M.Lam / (M.vbar * N * Einv M + 2 * M.Lam) ∧ effWage o = o.w := by
  have hE := Einv_pos M hM
  have hM' := hM
  obtain ⟨hv, hL, -, -, -, -, -, -⟩ := hM
  obtain ⟨hfeas, hmax⟩ := ho
  obtain ⟨hD, hS, hDS, -, hw, -, hprof⟩ := feas_dest M hM' hN hfeas
  obtain ⟨c, hc⟩ : ∃ c, c = 2 / (N * Einv M) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact div_pos two_pos (mul_pos hN hE)
  obtain ⟨a, ha_def⟩ : ∃ a, a = M.vbar / M.Lam + c := ⟨_, rfl⟩
  have ha : 0 < a := by have := div_pos hv hL; linarith
  have hPi : ∀ D S, PiDS M N D S = M.vbar * D - (a - c) * D ^ 2 - c * S ^ 2 := by
    intro D S; unfold PiDS priceDS; rw [h0, hc, ha_def, hc]; ring
  obtain ⟨D0, hD0⟩ : ∃ D0, D0 = M.vbar / (2 * a) := ⟨_, rfl⟩
  have hD00 : 0 < D0 := by rw [hD0]; exact div_pos hv (by linarith)
  have ha0 : a ≠ 0 := ha.ne'
  have hPi0 : PiDS M N D0 D0 = M.vbar ^ 2 / (4 * a) := by
    rw [hPi, hD0]; field_simp; ring
  obtain ⟨hf0, hp0⟩ := feas_mk M hM' hN hD00 le_rfl (fun h => absurd h0 h)
    (by rw [hPi0]; exact div_pos (pow_pos hv 2) (by linarith))
  have h1 := hmax _ hf0
  rw [hp0, hPi0, hprof] at h1
  have key : a * (o.D - D0) ^ 2 + c * (o.S ^ 2 - o.D ^ 2) =
      M.vbar ^ 2 / (4 * a) - PiDS M N o.D o.S := by
    rw [hPi, hD0]; field_simp; ring
  have hS2 : 0 ≤ o.S ^ 2 - o.D ^ 2 := by nlinarith
  have q1 := mul_nonneg ha.le (sq_nonneg (o.D - D0))
  have q2 := mul_nonneg hc0.le hS2
  have e1 : a * (o.D - D0) ^ 2 = 0 := by linarith
  have e2 : c * (o.S ^ 2 - o.D ^ 2) = 0 := by linarith
  have hDD : o.D = D0 := by
    have := (mul_eq_zero.1 e1).resolve_left ha.ne'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  have hSD : o.S = o.D := by
    have h3 := (mul_eq_zero.1 e2).resolve_left hc0.ne'
    have : (o.S - o.D) * (o.S + o.D) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hwD : o.w = c * D0 := by
    rw [hw, hSD, hDD, hc]
    have hN0 : N ≠ 0 := hN.ne'
    have hE0 : Einv M ≠ 0 := hE.ne'
    have : D0 ≠ 0 := hD00.ne'
    field_simp
  refine ⟨?_, ?_⟩
  · have hden : M.vbar * N * Einv M + 2 * M.Lam ≠ 0 := by
      have := mul_pos (mul_pos hv hN) hE; linarith
    rw [hwD, eq_div_iff hden]
    have hNE : M.vbar * N * Einv M = M.vbar * (2 / c) := by
      rw [hc]; have hN0 : N ≠ 0 := hN.ne'; have hE0 : Einv M ≠ 0 := hE.ne'; field_simp
    have haL : a * M.Lam = M.vbar + c * M.Lam := by
      rw [ha_def]; have := hL.ne'; field_simp
    rw [hNE, show M.vbar * (2 / c) + 2 * M.Lam = 2 * (a * M.Lam) / c by
      rw [haL]; have := hc0.ne'; field_simp, hD0]
    have := hc0.ne'
    field_simp
  · unfold effWage; rw [hSD]; exact mul_div_cancel_right₀ _ hD.ne'

lemma W0_anti (v L E : ℝ) (hv : 0 < v) (hL : 0 < L) (hE : 0 < E) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) : v * L / (v * b * E + 2 * L) < v * L / (v * a * E + 2 * L) := by
  have h1 : 0 < v * a * E + 2 * L := by have := mul_pos (mul_pos hv ha) hE; linarith
  have h2 : v * a * E + 2 * L < v * b * E + 2 * L := by
    have := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hab hv) hE; linarith
  exact div_lt_div_of_pos_left (mul_pos hv hL) h1 h2

lemma sq_step {x y E : ℝ} (hx : 0 < x) (hxy : x < y) (hE : 0 < E) :
    x ^ 2 * E / 4 < y ^ 2 * E / 4 := by
  have : x ^ 2 < y ^ 2 := by nlinarith
  have := mul_lt_mul_of_pos_right this hE
  linarith

lemma effWage_eq (M : Model) (hv : 0 < M.vbar) (o : Outcome) :
    effWage o = M.vbar / 2 * (util o * (2 * o.w / M.vbar)) := by
  unfold effWage util
  have := hv.ne'
  field_simp

end LW079

open LaborWelfare.PoolSize MeasureTheory Filter Topology in
theorem solution (M : Model) (hM : M.Std) (opt : ℝ → Outcome) (hopt : ∀ N, Nlow M < N → IsOptimal M N (opt N)) :
    (M.h = 0 →
        StrictAntiOn (fun N => (opt N).w) (Set.Ioi 0) ∧
        StrictAntiOn (fun N => effWage (opt N)) (Set.Ioi 0) ∧
        StrictAntiOn (fun N => avgLaborWelfare M N (opt N)) (Set.Ioi 0)) ∧
      (0 < M.h →
        StrictAntiOn (fun N => (opt N).w) (Set.Ioi (Nlow M)) ∧
        (∃ N₀, 0 < N₀ ∧ Nlow M < N₀ ∧
          StrictMonoOn (fun N => util (opt N)) (Set.Ioo (Nlow M) N₀) ∧
          StrictAntiOn (fun N => util (opt N)) (Set.Ioi N₀)) ∧
        (∃ N₀, 0 < N₀ ∧ Nlow M < N₀ ∧
          StrictMonoOn (fun N => effWage (opt N)) (Set.Ioo (Nlow M) N₀) ∧
          StrictAntiOn (fun N => effWage (opt N)) (Set.Ioi N₀)) ∧
        (∃ N₀, 0 < N₀ ∧ Nlow M < N₀ ∧
          StrictMonoOn (fun N => avgLaborWelfare M N (opt N)) (Set.Ioo (Nlow M) N₀) ∧
          StrictAntiOn (fun N => avgLaborWelfare M N (opt N)) (Set.Ioi N₀))) := by
  have hE := LW079.Einv_pos M hM
  have hM' := hM
  obtain ⟨hv, hL, hh, hβ, -, -, -, -⟩ := hM
  constructor
  · intro h0
    have hNlow : Nlow M = 0 := by unfold Nlow; split_ifs <;> simp [h0]
    have hch : ∀ N, 0 < N → (opt N).w = M.vbar * M.Lam / (M.vbar * N * Einv M + 2 * M.Lam) ∧
        effWage (opt N) = (opt N).w :=
      fun N hN => LW079.h0_char M hM' h0 hN (hopt N (by rw [hNlow]; exact hN))
    have hW : StrictAntiOn (fun N => (opt N).w) (Set.Ioi 0) := by
      intro a ha b hb hab
      show (opt b).w < (opt a).w
      rw [(hch a ha).1, (hch b hb).1]
      exact LW079.W0_anti _ _ _ hv hL hE ha hab
    have hpos : ∀ N, 0 < N → 0 < (opt N).w := by
      intro N hN; rw [(hch N hN).1]
      exact div_pos (mul_pos hv hL) (by have := mul_pos (mul_pos hv hN) hE; linarith)
    refine ⟨hW, ?_, ?_⟩
    · intro a ha b hb hab
      show effWage (opt b) < effWage (opt a)
      rw [(hch a ha).2, (hch b hb).2]
      exact hW ha hb hab
    · intro a ha b hb hab
      show avgLaborWelfare M b (opt b) < avgLaborWelfare M a (opt a)
      have ha' : (0:ℝ) < a := ha
      have hb' : (0:ℝ) < b := hb
      rw [LW079.avgLW_eq M ha'.ne', LW079.avgLW_eq M hb'.ne', (hch a ha).2, (hch b hb).2]
      exact LW079.sq_step (hpos b hb) (hW ha hb hab) hE
  · intro hpos
    have hC : 0 < 2 * M.h / (M.vbar * M.Lam) := div_pos (by linarith) (mul_pos hv hL)
    have hK : 0 < 2 * M.Lam / (Einv M * M.vbar) := div_pos (by linarith) (mul_pos hE hv)
    have hch := fun N (hN : Nlow M < N) => LW079.char_pos M hM' hpos hN (hopt N hN)
    have hlow : ∀ s ρ, LW079.CP (2 * M.h / (M.vbar * M.Lam)) M.beta s ρ →
        Nlow M < LW079.Nf (2 * M.Lam / (Einv M * M.vbar)) s ρ := by
      intro s ρ p
      unfold Nlow
      split_ifs with hb1
      · have hk := p.eq
        unfold LW079.kf at hk
        rw [hb1, sub_self, Real.rpow_zero, mul_one] at hk
        have hs0 := p.s0
        have hs1 := p.s1
        have hr0 := p.r0
        have hr1 := p.r1
        have h1r : 0 < 1 - ρ := by linarith
        have i1 : 1 < (1 - ρ)⁻¹ := (one_lt_inv₀ h1r).2 (by linarith)
        have i2 : 1 < ((1 - ρ) ^ 2)⁻¹ := (one_lt_inv₀ (by positivity)).2 (by nlinarith)
        have hq2 : 2 * s ^ 2 < LW079.qf 1 ρ := by
          unfold LW079.qf; nlinarith
        unfold LW079.Nf
        rw [div_lt_div_iff₀ (mul_pos (pow_pos hv 2) hE) (mul_pos hs0 (pow_pos hr0 2))]
        have hR : 2 * M.Lam / (Einv M * M.vbar) * (1 - s) * (M.vbar ^ 2 * Einv M) =
            2 * M.Lam * M.vbar * (1 - s) := by
          have := hv.ne'; have := hE.ne'; field_simp
        rw [hR]
        have heq : 2 * M.Lam * M.vbar * (s * (1 - s)) = 4 * M.h * ρ ^ 2 * LW079.qf 1 ρ := by
          rw [hk]; have := hv.ne'; have := hL.ne'; field_simp; ring
        have hm := mul_lt_mul_of_pos_left hq2 (mul_pos (mul_pos four_pos hpos) (pow_pos hr0 2))
        have : 8 * M.h * (s * ρ ^ 2) * s < 2 * M.Lam * M.vbar * (1 - s) * s := by
          nlinarith
        exact lt_of_mul_lt_mul_right this hs0.le
      · exact LW079.Nf_pos hK p
    obtain ⟨hA, hU, ⟨N1, hN1, hN1l, hm1, ha1⟩⟩ := LW079.assemble hC hβ hK
      (fun N => 2 * (opt N).w / M.vbar) (fun N => util (opt N))
      (fun N hN => (hch N hN).1) (fun N hN => (hch N hN).2) hlow
    have hN0 : 0 ≤ Nlow M := LW079.Nlow_nonneg M hv hh hE
    have hepos : ∀ N, Nlow M < N → 0 < effWage (opt N) := by
      intro N hN
      rw [LW079.effWage_eq M hv]
      exact mul_pos (div_pos hv two_pos) (mul_pos (hch N hN).1.r0 (hch N hN).1.s0)
    refine ⟨?_, hU, ⟨N1, hN1, hN1l, ?_, ?_⟩, ⟨N1, hN1, hN1l, ?_, ?_⟩⟩
    · intro a ha b hb hab
      have := hA ha hb hab
      simp only at this
      rw [div_lt_div_iff_of_pos_right hv] at this
      show (opt b).w < (opt a).w
      linarith
    · intro a ha b hb hab
      have := hm1 ha hb hab
      simp only at this
      show effWage (opt a) < effWage (opt b)
      rw [LW079.effWage_eq M hv, LW079.effWage_eq M hv]
      exact mul_lt_mul_of_pos_left this (div_pos hv two_pos)
    · intro a ha b hb hab
      have := ha1 ha hb hab
      simp only at this
      show effWage (opt b) < effWage (opt a)
      rw [LW079.effWage_eq M hv, LW079.effWage_eq M hv]
      exact mul_lt_mul_of_pos_left this (div_pos hv two_pos)
    · intro a ha b hb hab
      have := hm1 ha hb hab
      simp only at this
      show avgLaborWelfare M a (opt a) < avgLaborWelfare M b (opt b)
      have ha' : 0 < a := lt_of_le_of_lt hN0 ha.1
      have hb' : 0 < b := lt_of_le_of_lt hN0 hb.1
      rw [LW079.avgLW_eq M ha'.ne', LW079.avgLW_eq M hb'.ne']
      have hlt : effWage (opt a) < effWage (opt b) := by
        rw [LW079.effWage_eq M hv, LW079.effWage_eq M hv]
        exact mul_lt_mul_of_pos_left this (div_pos hv two_pos)
      exact LW079.sq_step (hepos a ha.1) hlt hE
    · intro a ha b hb hab
      have := ha1 ha hb hab
      simp only at this
      show avgLaborWelfare M b (opt b) < avgLaborWelfare M a (opt a)
      have ha2 : Nlow M < a := lt_trans hN1l ha
      have hb2 : Nlow M < b := lt_trans hN1l hb
      have ha' : 0 < a := lt_of_le_of_lt hN0 ha2
      have hb' : 0 < b := lt_of_le_of_lt hN0 hb2
      rw [LW079.avgLW_eq M ha'.ne', LW079.avgLW_eq M hb'.ne']
      have hlt : effWage (opt b) < effWage (opt a) := by
        rw [LW079.effWage_eq M hv, LW079.effWage_eq M hv]
        exact mul_lt_mul_of_pos_left this (div_pos hv two_pos)
      exact LW079.sq_step (hepos b hb2) hlt hE
