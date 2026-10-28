-- Prove2me | solution 1 for HedgeInv.Order.proposition7_order_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T15:38:12.187797+00:00
-- url     : https://prove2.me/submissions/28c0fcc6-4c25-495d-b2d4-ed3fe3e3ca6b

import Mathlib
import Definitions.Def_HedgeInv_Order_Model

set_option autoImplicit false

namespace HedgeInvP561

open MeasureTheory HedgeInv.Order

lemma G_anti_U (g : ℝ → ℝ) (hg : Antitone g)
    (hconv : ∀ d ≤ 0, Antitone (fun x => g (x + d) - g x))
    (B1 B2 V Δ : ℝ) (hκ : B2 ≤ B1) (hΔ : 0 ≤ Δ) {U1 U2 : ℝ} (hU : U1 ≤ U2) :
    g (B2 + min U2 (V + Δ)) - g (B1 + min U2 V) ≤
      g (B2 + min U1 (V + Δ)) - g (B1 + min U1 V) := by
  have case1 : ∀ x y, x ≤ y → y ≤ V →
      g (B2 + min y (V + Δ)) - g (B1 + min y V) ≤
        g (B2 + min x (V + Δ)) - g (B1 + min x V) := by
    intro x y hxy hyV
    have hx : x ≤ V := hxy.trans hyV
    rw [min_eq_left (by linarith), min_eq_left hyV, min_eq_left (by linarith), min_eq_left hx]
    have h := hconv (B2 - B1) (by linarith) (show B1 + x ≤ B1 + y by linarith)
    simp only at h
    have e1 : B1 + y + (B2 - B1) = B2 + y := by ring
    have e2 : B1 + x + (B2 - B1) = B2 + x := by ring
    rw [e1, e2] at h
    exact h
  have case2 : ∀ x y, x ≤ y → V ≤ x →
      g (B2 + min y (V + Δ)) - g (B1 + min y V) ≤
        g (B2 + min x (V + Δ)) - g (B1 + min x V) := by
    intro x y hxy hVx
    rw [min_eq_right hVx, min_eq_right (hVx.trans hxy)]
    have : g (B2 + min y (V + Δ)) ≤ g (B2 + min x (V + Δ)) :=
      hg (by have := min_le_min hxy (le_refl (V + Δ)); linarith)
    linarith
  rcases le_total U2 V with h | h
  · exact case1 _ _ hU h
  rcases le_total V U1 with h' | h'
  · exact case2 _ _ hU h'
  · exact (case2 V U2 h le_rfl).trans (case1 U1 V h' le_rfl)

lemma G_mono_V (g : ℝ → ℝ) (hg : Antitone g)
    (hconv : ∀ d ≥ 0, Monotone (fun x => g (x + d) - g x))
    (B1 B2 U Δ : ℝ) (hΔ : 0 ≤ Δ) (hd : 0 ≤ Δ + (B2 - B1)) {V1 V2 : ℝ} (hV : V2 ≤ V1) :
    g (B2 + min U (V2 + Δ)) - g (B1 + min U V2) ≤
      g (B2 + min U (V1 + Δ)) - g (B1 + min U V1) := by
  have case1 : ∀ x y, x ≤ y → y + Δ ≤ U →
      g (B2 + min U (x + Δ)) - g (B1 + min U x) ≤
        g (B2 + min U (y + Δ)) - g (B1 + min U y) := by
    intro x y hxy hy
    rw [min_eq_right hy, min_eq_right (show y ≤ U by linarith),
      min_eq_right (show x + Δ ≤ U by linarith), min_eq_right (show x ≤ U by linarith)]
    have h := hconv (Δ + (B2 - B1)) hd (show B1 + x ≤ B1 + y by linarith)
    simp only at h
    have e1 : B1 + y + (Δ + (B2 - B1)) = B2 + (y + Δ) := by ring
    have e2 : B1 + x + (Δ + (B2 - B1)) = B2 + (x + Δ) := by ring
    rw [e1, e2] at h
    exact h
  have case2 : ∀ x y, x ≤ y → U ≤ x + Δ →
      g (B2 + min U (x + Δ)) - g (B1 + min U x) ≤
        g (B2 + min U (y + Δ)) - g (B1 + min U y) := by
    intro x y hxy hU
    rw [min_eq_left hU, min_eq_left (show U ≤ y + Δ by linarith)]
    have : g (B1 + min U y) ≤ g (B1 + min U x) :=
      hg (by have := min_le_min (le_refl U) hxy; linarith)
    linarith
  rcases le_total (V1 + Δ) U with h | h
  · exact case1 _ _ hV h
  rcases le_total U (V2 + Δ) with h' | h'
  · exact case2 _ _ hV h'
  · exact (case1 V2 (U - Δ) (by linarith) (by linarith)).trans
      (case2 (U - Δ) V1 (by linarith) (by linarith))

lemma hp_eq (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r I t s e : ℝ) :
    hedgedPayoff W a b c₁ φ x0r I t s e =
      (W - c₁ * I + t * x0r) + min (s + e - t * φ s) ((I - a) / b - t * φ s) := by
  unfold hedgedPayoff
  rw [min_sub_sub_right]
  ring

lemma G_s_anti (g : ℝ → ℝ) (hg : Antitone g)
    (hc1 : ∀ d ≤ 0, Antitone (fun x => g (x + d) - g x))
    (hc2 : ∀ d ≥ 0, Monotone (fun x => g (x + d) - g x))
    (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r I1 I2 t e : ℝ) (hb : 0 < b) (hc : 0 < c₁)
    (hcb : c₁ * b < 1) (hI : I1 ≤ I2) (ht : 0 ≤ t) (hφ : Monotone φ) {s1 s2 : ℝ}
    (hs : s1 ≤ s2) (hlip : t * (φ s2 - φ s1) ≤ s2 - s1) :
    g (hedgedPayoff W a b c₁ φ x0r I2 t s2 e) - g (hedgedPayoff W a b c₁ φ x0r I1 t s2 e) ≤
      g (hedgedPayoff W a b c₁ φ x0r I2 t s1 e) - g (hedgedPayoff W a b c₁ φ x0r I1 t s1 e) := by
  simp only [hp_eq]
  set Δ := (I2 - a) / b - (I1 - a) / b with hΔdef
  have hsplit : ∀ s, (I2 - a) / b - t * φ s = ((I1 - a) / b - t * φ s) + Δ := by
    intro s; rw [hΔdef]; ring
  rw [hsplit s1, hsplit s2]
  have hΔ : Δ = (I2 - I1) / b := by rw [hΔdef]; field_simp; ring
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; exact div_nonneg (by linarith) hb.le
  have hd : 0 ≤ Δ + ((W - c₁ * I2 + t * x0r) - (W - c₁ * I1 + t * x0r)) := by
    have : Δ + ((W - c₁ * I2 + t * x0r) - (W - c₁ * I1 + t * x0r)) =
        (I2 - I1) * (1 - c₁ * b) / b := by rw [hΔ]; field_simp; ring
    rw [this]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hb.le
  have hB : W - c₁ * I2 + t * x0r ≤ W - c₁ * I1 + t * x0r := by nlinarith
  have hU : s1 + e - t * φ s1 ≤ s2 + e - t * φ s2 := by
    have : t * (φ s2 - φ s1) = t * φ s2 - t * φ s1 := by ring
    linarith
  have hV : (I1 - a) / b - t * φ s2 ≤ (I1 - a) / b - t * φ s1 := by
    have := mul_le_mul_of_nonneg_left (hφ hs) ht
    linarith
  exact (G_anti_U g hg hc1 _ _ _ Δ hB hΔ0 hU).trans (G_mono_V g hg hc2 _ _ _ Δ hΔ0 hd hV)

lemma u_facts (u : ℝ → ℝ) (hu : IsDARADAPUtility u) :
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧ Continuous (deriv u) ∧
      Antitone (deriv u) ∧ Monotone (deriv (deriv u)) := by
  have h1 : Differentiable ℝ u := hu.contDiff.differentiable (by norm_num)
  have h3' : ContDiff ℝ ((2 : WithTop ℕ∞) + 1) u := by
    convert hu.contDiff using 1
    rfl
  have h2c : ContDiff ℝ 2 (deriv u) := (contDiff_succ_iff_deriv.mp h3').2.2
  have h2 : Differentiable ℝ (deriv u) := h2c.differentiable (by norm_num)
  have h3 : Continuous (deriv u) := h2.continuous
  have h4 : Antitone (deriv u) := antitone_of_deriv_nonpos h2 (fun x => (hu.deriv2_neg x).le)
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro x y hxy
  have hR : ∀ w, -(deriv (deriv u) w) =
      MDPFinance.FinancialMarkets.arrowPrattCoefficient u w * deriv u w := by
    intro w
    unfold MDPFinance.FinancialMarkets.arrowPrattCoefficient
    have := hu.deriv_pos w
    field_simp
  have hR0 : ∀ w, 0 ≤ MDPFinance.FinancialMarkets.arrowPrattCoefficient u w := by
    intro w
    unfold MDPFinance.FinancialMarkets.arrowPrattCoefficient
    exact div_nonneg (by linarith [hu.deriv2_neg w]) (hu.deriv_pos w).le
  have hd := hu.dara hxy
  have k1 : MDPFinance.FinancialMarkets.arrowPrattCoefficient u y * deriv u y ≤
      MDPFinance.FinancialMarkets.arrowPrattCoefficient u x * deriv u y :=
    mul_le_mul_of_nonneg_right hd (hu.deriv_pos y).le
  have k2 : MDPFinance.FinancialMarkets.arrowPrattCoefficient u x * deriv u y ≤
      MDPFinance.FinancialMarkets.arrowPrattCoefficient u x * deriv u x :=
    mul_le_mul_of_nonneg_left (h4 hxy) (hR0 x)
  linarith [hR x, hR y]

lemma shift_diff (g : ℝ → ℝ) (hg : Differentiable ℝ g) (hm : Monotone (deriv g)) :
    (∀ d ≤ 0, Antitone (fun x => g (x + d) - g x)) ∧
      (∀ d ≥ 0, Monotone (fun x => g (x + d) - g x)) := by
  have hD : ∀ d x, HasDerivAt (fun x => g (x + d) - g x) (deriv g (x + d) - deriv g x) x := by
    intro d x
    have h1 : HasDerivAt (fun x => g (x + d)) (deriv g (x + d)) x :=
      HasDerivAt.comp_add_const x d (hg (x + d)).hasDerivAt
    exact h1.sub (hg x).hasDerivAt
  constructor
  · intro d hd
    apply antitone_of_deriv_nonpos (fun x => (hD d x).differentiableAt)
    intro x
    rw [(hD d x).deriv]
    linarith [hm (show x + d ≤ x by linarith)]
  · intro d hd
    apply monotone_of_deriv_nonneg (fun x => (hD d x).differentiableAt)
    intro x
    rw [(hD d x).deriv]
    linarith [hm (show x ≤ x + d by linarith)]

lemma cont_t (u : ℝ → ℝ) (hcu : Continuous (deriv u)) (W a b c₁ : ℝ) (φ : ℝ → ℝ)
    (x0r I s e : ℝ) :
    Continuous (fun t => deriv u (hedgedPayoff W a b c₁ φ x0r I t s e)) := by
  unfold hedgedPayoff
  fun_prop

lemma ftc_alpha (u : ℝ → ℝ) (hud : Differentiable ℝ u) (hcu : Continuous (deriv u))
    (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r I α1 α2 s e : ℝ) :
    ∫ t in α1..α2, deriv u (hedgedPayoff W a b c₁ φ x0r I t s e) * (x0r - φ s) =
      u (hedgedPayoff W a b c₁ φ x0r I α2 s e) - u (hedgedPayoff W a b c₁ φ x0r I α1 s e) := by
  have hlin : ∀ t, hedgedPayoff W a b c₁ φ x0r I t s e =
      (W + min (s + e) ((I - a) / b) - c₁ * I) + t * (x0r - φ s) := by
    intro t; unfold hedgedPayoff; ring
  simp only [hlin]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    have h1 : HasDerivAt (fun t => (W + min (s + e) ((I - a) / b) - c₁ * I) + t * (x0r - φ s))
        (x0r - φ s) t := by
      simpa using ((hasDerivAt_id t).mul_const (x0r - φ s)).const_add
        (W + min (s + e) ((I - a) / b) - c₁ * I)
    exact (hud _).hasDerivAt.comp t h1
  · apply Continuous.intervalIntegrable
    exact (hcu.comp (continuous_const.add (continuous_id.mul continuous_const))).mul
      continuous_const

lemma four_point (u : ℝ → ℝ) (hud : Differentiable ℝ u) (hcu : Continuous (deriv u))
    (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r I1 I2 α1 α2 s e : ℝ) :
    u (hedgedPayoff W a b c₁ φ x0r I2 α2 s e) - u (hedgedPayoff W a b c₁ φ x0r I1 α2 s e) -
        u (hedgedPayoff W a b c₁ φ x0r I2 α1 s e) + u (hedgedPayoff W a b c₁ φ x0r I1 α1 s e) =
      (x0r - φ s) * ∫ t in α1..α2, (deriv u (hedgedPayoff W a b c₁ φ x0r I2 t s e) -
        deriv u (hedgedPayoff W a b c₁ φ x0r I1 t s e)) := by
  have h2 := ftc_alpha u hud hcu W a b c₁ φ x0r I2 α1 α2 s e
  have h1 := ftc_alpha u hud hcu W a b c₁ φ x0r I1 α1 α2 s e
  rw [intervalIntegral.integral_mul_const] at h1 h2
  rw [intervalIntegral.integral_sub ((cont_t u hcu W a b c₁ φ x0r I2 s e).intervalIntegrable _ _)
    ((cont_t u hcu W a b c₁ φ x0r I1 s e).intervalIntegrable _ _)]
  linear_combination h1 - h2

lemma lip_of_alphaBar (ν G : Measure ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r αbar : ℝ)
    (hstd : StandingAssumptions ν G b c₁ φ x0r)
    (hαbar : AlphaBarCond G W a b c₁ φ x0r αbar)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) αbar) {s1 s2 : ℝ} (hs : s1 ≤ s2) :
    t * (φ s2 - φ s1) ≤ s2 - s1 := by
  haveI := hstd.probG
  have hI0 : max a 0 < max a 0 + 1 := lt_add_one _
  have hle := hαbar.2 t ht (max a 0 + 1) hI0 hs
  unfold condMeanPayoff at hle
  have hint_e : Integrable (fun e : ℝ => e) G := hstd.memLp_two.integrable (by norm_num)
  have hint : ∀ s, Integrable (fun e => hedgedPayoff W a b c₁ φ x0r (max a 0 + 1) t s e) G := by
    intro s
    have hm : Integrable (fun e => min (s + e) ((max a 0 + 1 - a) / b)) G := by
      refine Integrable.mono' ((integrable_const (|s| + |(max a 0 + 1 - a) / b|)).add hint_e.abs)
        (by fun_prop) ?_
      refine Filter.Eventually.of_forall (fun e => ?_)
      simp only [Real.norm_eq_abs]
      calc |min (s + e) ((max a 0 + 1 - a) / b)| ≤ max |s + e| |(max a 0 + 1 - a) / b| :=
            abs_min_le_max_abs_abs
        _ ≤ |s| + |(max a 0 + 1 - a) / b| + |e| := by
            apply max_le
            · linarith [abs_add_le s e, abs_nonneg ((max a 0 + 1 - a) / b)]
            · linarith [abs_nonneg s, abs_nonneg e]
    unfold hedgedPayoff
    exact ((((integrable_const W).add hm).sub (integrable_const _)).sub
      (integrable_const _)).add (integrable_const _)
  have hpt : ∀ e, hedgedPayoff W a b c₁ φ x0r (max a 0 + 1) t s2 e ≤
      hedgedPayoff W a b c₁ φ x0r (max a 0 + 1) t s1 e + ((s2 - s1) - t * (φ s2 - φ s1)) := by
    intro e
    unfold hedgedPayoff
    have hmin : min (s2 + e) ((max a 0 + 1 - a) / b) ≤
        min (s1 + e) ((max a 0 + 1 - a) / b) + (s2 - s1) := by
      rcases le_total (s1 + e) ((max a 0 + 1 - a) / b) with h | h
      · rw [min_eq_left h]
        linarith [min_le_left (s2 + e) ((max a 0 + 1 - a) / b)]
      · rw [min_eq_right h]
        linarith [min_le_right (s2 + e) ((max a 0 + 1 - a) / b)]
    have := mul_sub t (φ s2) (φ s1)
    linarith
  have hI2 : ∫ e, hedgedPayoff W a b c₁ φ x0r (max a 0 + 1) t s2 e ∂G ≤
      ∫ e, (hedgedPayoff W a b c₁ φ x0r (max a 0 + 1) t s1 e + ((s2 - s1) - t * (φ s2 - φ s1))) ∂G :=
    integral_mono (hint s2) ((hint s1).add (integrable_const _)) hpt
  rw [integral_add (hint s1) (integrable_const _), integral_const] at hI2
  simp at hI2
  linarith

lemma cheb (ν : Measure ℝ) [IsProbabilityMeasure ν] (δ N : ℝ → ℝ) (hδ : Antitone δ)
    (hN : Antitone N) (hδi : Integrable δ ν) (hδ0 : ∫ s, δ s ∂ν = 0)
    (hint : Integrable (fun s => δ s * N s) ν) :
    0 ≤ ∫ s, δ s * N s ∂ν := by
  by_cases hpos : ∃ s, 0 < δ s
  · by_cases hneg : ∃ s, δ s < 0
    · obtain ⟨s0, hs0⟩ := hneg
      have hlt : ∀ s s', 0 < δ s → δ s' < 0 → s ≤ s' := by
        intro s s' hs hs'
        by_contra hcon
        push Not at hcon
        have := hδ hcon.le
        linarith
      have hne : (N '' {s | 0 < δ s}).Nonempty := by
        obtain ⟨s1, h1⟩ := hpos
        exact ⟨_, s1, h1, rfl⟩
      have hbdd : BddBelow (N '' {s | 0 < δ s}) := by
        refine ⟨N s0, ?_⟩
        rintro _ ⟨s, hs, rfl⟩
        exact hN (hlt s s0 hs hs0)
      have hpt : ∀ s, 0 ≤ δ s * (N s - sInf (N '' {s | 0 < δ s})) := by
        intro s
        rcases lt_trichotomy (δ s) 0 with h | h | h
        · have : N s ≤ sInf (N '' {s | 0 < δ s}) := by
            apply le_csInf hne
            rintro _ ⟨s', hs', rfl⟩
            exact hN (hlt s' s hs' h)
          nlinarith
        · simp [h]
        · have : sInf (N '' {s | 0 < δ s}) ≤ N s := csInf_le hbdd ⟨s, h, rfl⟩
          nlinarith
      have heq : ∫ s, δ s * (N s - sInf (N '' {s | 0 < δ s})) ∂ν = ∫ s, δ s * N s ∂ν := by
        have h2 : (fun s => δ s * (N s - sInf (N '' {s | 0 < δ s}))) =
            fun s => δ s * N s - δ s * sInf (N '' {s | 0 < δ s}) := by
          funext s; ring
        rw [h2, integral_sub hint (hδi.mul_const _), integral_mul_const, hδ0]
        simp
      rw [← heq]
      exact integral_nonneg hpt
    · push Not at hneg
      have hz : δ =ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg hneg hδi).mp hδ0
      have : (fun s => δ s * N s) =ᵐ[ν] 0 := hz.mono (fun s hs => by simp [hs])
      rw [integral_congr_ae this]
      simp
  · push Not at hpos
    have hz' : (fun s => -δ s) =ᵐ[ν] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun s => by simp only [Pi.zero_apply, Pi.neg_apply]; linarith [hpos s])
        hδi.neg).mp (by simp only [Pi.neg_apply]; rw [integral_neg, hδ0]; simp)
    have : (fun s => δ s * N s) =ᵐ[ν] 0 := hz'.mono (fun s hs => by
      simp only [Pi.zero_apply, neg_eq_zero] at hs
      simp [hs])
    rw [integral_congr_ae this]
    simp

lemma supermod (ν G : Measure ℝ) (u : ℝ → ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r αbar : ℝ)
    (hstd : StandingAssumptions ν G b c₁ φ x0r) (hu : IsDARADAPUtility u)
    (hαbar : AlphaBarCond G W a b c₁ φ x0r αbar)
    (hreg : RegularityCond ν G u W a b c₁ φ x0r αbar)
    {I1 I2 α1 α2 : ℝ} (hI1 : max a 0 < I1) (hI12 : I1 ≤ I2)
    (hα1 : α1 ∈ Set.Icc (0 : ℝ) αbar) (hα2 : α2 ∈ Set.Icc (0 : ℝ) αbar) (h12 : α1 ≤ α2) :
    expUtil ν G u W a b c₁ φ x0r I2 α1 - expUtil ν G u W a b c₁ φ x0r I1 α1 ≤
      expUtil ν G u W a b c₁ φ x0r I2 α2 - expUtil ν G u W a b c₁ φ x0r I1 α2 := by
  haveI := hstd.probν
  haveI := hstd.probG
  obtain ⟨hud, hud', hcu, hanti, hmono⟩ := u_facts u hu
  obtain ⟨hc1, hc2⟩ := shift_diff (deriv u) hud' hmono
  have hI2 : max a 0 < I2 := lt_of_lt_of_le hI1 hI12
  have i11 := (hreg I1 hI1 α1 hα1).1
  have i12 := (hreg I1 hI1 α2 hα2).1
  have i21 := (hreg I2 hI2 α1 hα1).1
  have i22 := (hreg I2 hI2 α2 hα2).1
  let F : ℝ × ℝ → ℝ := fun p =>
    u (hedgedPayoff W a b c₁ φ x0r I2 α2 p.1 p.2) - u (hedgedPayoff W a b c₁ φ x0r I1 α2 p.1 p.2) -
      u (hedgedPayoff W a b c₁ φ x0r I2 α1 p.1 p.2) + u (hedgedPayoff W a b c₁ φ x0r I1 α1 p.1 p.2)
  have hFi : Integrable F (ν.prod G) := ((i22.sub i12).sub i21).add i11
  have hFint : ∫ p, F p ∂(ν.prod G) =
      expUtil ν G u W a b c₁ φ x0r I2 α2 - expUtil ν G u W a b c₁ φ x0r I1 α2 -
        expUtil ν G u W a b c₁ φ x0r I2 α1 + expUtil ν G u W a b c₁ φ x0r I1 α1 := by
    have j1 : Integrable (fun p : ℝ × ℝ => u (hedgedPayoff W a b c₁ φ x0r I2 α2 p.1 p.2) -
        u (hedgedPayoff W a b c₁ φ x0r I1 α2 p.1 p.2)) (ν.prod G) := i22.sub i12
    have j2 : Integrable (fun p : ℝ × ℝ => u (hedgedPayoff W a b c₁ φ x0r I2 α2 p.1 p.2) -
        u (hedgedPayoff W a b c₁ φ x0r I1 α2 p.1 p.2) -
        u (hedgedPayoff W a b c₁ φ x0r I2 α1 p.1 p.2)) (ν.prod G) := j1.sub i21
    unfold expUtil
    rw [← integral_sub i22 i12, ← integral_sub j1 i21, ← integral_add j2 i11]
  have hnonneg : 0 ≤ ∫ p, F p ∂(ν.prod G) := by
    rw [integral_prod_symm F hFi]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hFi.prod_left_ae] with e he
    let N : ℝ → ℝ := fun s => ∫ t in α1..α2, (deriv u (hedgedPayoff W a b c₁ φ x0r I2 t s e) -
        deriv u (hedgedPayoff W a b c₁ φ x0r I1 t s e))
    have hFN : (fun s => F (s, e)) = fun s => (x0r - φ s) * N s := by
      funext s
      exact four_point u hud hcu W a b c₁ φ x0r I1 I2 α1 α2 s e
    have hgoal : 0 ≤ ∫ s, (x0r - φ s) * N s ∂ν := by
      apply cheb ν (fun s => x0r - φ s) N
      · intro x y hxy
        have := hstd.mono hxy
        simp only
        linarith
      · intro s1 s2 hs
        apply intervalIntegral.integral_mono_on h12
        · exact ((cont_t u hcu W a b c₁ φ x0r I2 s2 e).sub
            (cont_t u hcu W a b c₁ φ x0r I1 s2 e)).intervalIntegrable _ _
        · exact ((cont_t u hcu W a b c₁ φ x0r I2 s1 e).sub
            (cont_t u hcu W a b c₁ φ x0r I1 s1 e)).intervalIntegrable _ _
        intro t ht
        have htI : t ∈ Set.Icc (0 : ℝ) αbar := ⟨hα1.1.trans ht.1, ht.2.trans hα2.2⟩
        exact G_s_anti (deriv u) hanti hc1 hc2 W a b c₁ φ x0r I1 I2 t e hstd.b_pos hstd.c₁_pos
          hstd.c₁b_lt_one hI12 htI.1 hstd.mono hs
          (lip_of_alphaBar ν G W a b c₁ φ x0r αbar hstd hαbar htI hs)
      · exact (integrable_const x0r).sub hstd.integrable
      · rw [integral_sub (integrable_const _) hstd.integrable, integral_const, hstd.fair]
        simp
      · rw [← hFN]; exact he
    have : ∫ s, F (s, e) ∂ν = ∫ s, (x0r - φ s) * N s ∂ν := by rw [hFN]
    simpa [this] using hgoal
  linarith [hFint, hnonneg]

lemma min_mid (y k1 k2 : ℝ) : (min y k1 + min y k2) / 2 ≤ min y ((k1 + k2) / 2) := by
  rcases le_total y k1 with h1 | h1 <;> rcases le_total y k2 with h2 | h2 <;>
    rcases le_total y ((k1 + k2) / 2) with h3 | h3 <;>
    simp only [min_eq_left, min_eq_right, h1, h2, h3] <;> linarith

lemma pt_strict (u : ℝ → ℝ) (hu : IsDARADAPUtility u) (W a b c₁ : ℝ) (φ : ℝ → ℝ)
    (x0r α s e I1 I2 : ℝ) (hb : 0 < b) (hc : 0 < c₁) (hcb : c₁ * b < 1) (h12 : I1 < I2) :
    (u (hedgedPayoff W a b c₁ φ x0r I1 α s e) + u (hedgedPayoff W a b c₁ φ x0r I2 α s e)) / 2 <
      u (hedgedPayoff W a b c₁ φ x0r ((I1 + I2) / 2) α s e) := by
  obtain ⟨hud, -, -, -, -⟩ := u_facts u hu
  have hsc : StrictConcaveOn ℝ Set.univ u :=
    strictConcaveOn_univ_of_deriv2_neg hud.continuous (fun x => by
      simpa [Function.iterate_succ] using hu.deriv2_neg x)
  have hsm : StrictMono u := strictMono_of_deriv_pos (fun x => hu.deriv_pos x)
  have hmidc : ∀ x y : ℝ, (u x + u y) / 2 ≤ u ((x + y) / 2) := by
    intro x y
    have := hsc.concaveOn.2 (Set.mem_univ x) (Set.mem_univ y) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e1 : (1 / 2 : ℝ) * x + 1 / 2 * y = (x + y) / 2 := by ring
    rw [e1] at this
    linarith
  have hmids : ∀ x y : ℝ, x ≠ y → (u x + u y) / 2 < u ((x + y) / 2) := by
    intro x y hxy
    have := hsc.2 (Set.mem_univ x) (Set.mem_univ y) hxy (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e1 : (1 / 2 : ℝ) * x + 1 / 2 * y = (x + y) / 2 := by ring
    rw [e1] at this
    linarith
  set C := W - α * φ s + α * x0r with hC
  set y := s + e with hy
  set k1 := (I1 - a) / b with hk1
  set k2 := (I2 - a) / b with hk2
  have hkm : ((I1 + I2) / 2 - a) / b = (k1 + k2) / 2 := by rw [hk1, hk2]; field_simp; ring
  have hk : k2 - k1 = (I2 - I1) / b := by rw [hk1, hk2]; field_simp; ring
  have hk12 : k1 < k2 := by
    have : 0 < (I2 - I1) / b := div_pos (by linarith) hb
    linarith
  have e1 : hedgedPayoff W a b c₁ φ x0r I1 α s e = C + (min y k1 - c₁ * I1) := by
    unfold hedgedPayoff; rw [hC, hy, hk1]; ring
  have e2 : hedgedPayoff W a b c₁ φ x0r I2 α s e = C + (min y k2 - c₁ * I2) := by
    unfold hedgedPayoff; rw [hC, hy, hk2]; ring
  have em : hedgedPayoff W a b c₁ φ x0r ((I1 + I2) / 2) α s e =
      C + (min y ((k1 + k2) / 2) - c₁ * ((I1 + I2) / 2)) := by
    unfold hedgedPayoff; rw [hkm, hC, hy]; ring
  rw [e1, e2, em]
  have hge : ((C + (min y k1 - c₁ * I1)) + (C + (min y k2 - c₁ * I2))) / 2 ≤
      C + (min y ((k1 + k2) / 2) - c₁ * ((I1 + I2) / 2)) := by
    have := min_mid y k1 k2
    linarith
  have hor : (C + (min y k1 - c₁ * I1)) ≠ (C + (min y k2 - c₁ * I2)) ∨
      ((C + (min y k1 - c₁ * I1)) + (C + (min y k2 - c₁ * I2))) / 2 <
        C + (min y ((k1 + k2) / 2) - c₁ * ((I1 + I2) / 2)) := by
    rcases le_or_gt y k1 with h | h
    · left
      intro heq
      rw [min_eq_left h, min_eq_left (h.trans hk12.le)] at heq
      nlinarith
    rcases le_or_gt k2 y with h' | h'
    · left
      intro heq
      rw [min_eq_right h', min_eq_right (hk12.le.trans h')] at heq
      have hpos : 0 < (I2 - I1) / b - c₁ * (I2 - I1) := by
        have : (I2 - I1) / b - c₁ * (I2 - I1) = (I2 - I1) * (1 - c₁ * b) / b := by
          field_simp
        rw [this]
        exact div_pos (mul_pos (by linarith) (by linarith)) hb
      linarith
    · right
      rw [min_eq_right h.le, min_eq_left h'.le]
      rcases le_total y ((k1 + k2) / 2) with h'' | h''
      · rw [min_eq_left h'']; linarith
      · rw [min_eq_right h'']; linarith
  rcases hor with hne | hlt
  · exact lt_of_lt_of_le (hmids _ _ hne) (hsm.monotone hge)
  · exact lt_of_le_of_lt (hmidc _ _) (hsm hlt)

lemma strict_mid (ν G : Measure ℝ) (u : ℝ → ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r αbar : ℝ)
    (hstd : StandingAssumptions ν G b c₁ φ x0r) (hu : IsDARADAPUtility u)
    (hreg : RegularityCond ν G u W a b c₁ φ x0r αbar)
    {I1 I2 α : ℝ} (hI1 : max a 0 < I1) (h12 : I1 < I2) (hα : α ∈ Set.Icc (0 : ℝ) αbar) :
    (expUtil ν G u W a b c₁ φ x0r I1 α + expUtil ν G u W a b c₁ φ x0r I2 α) / 2 <
      expUtil ν G u W a b c₁ φ x0r ((I1 + I2) / 2) α := by
  haveI := hstd.probν
  haveI := hstd.probG
  have hm : max a 0 < (I1 + I2) / 2 := by linarith
  have i1 := (hreg I1 hI1 α hα).1
  have i2 := (hreg I2 (by linarith) α hα).1
  have im := (hreg _ hm α hα).1
  have hlhs : (expUtil ν G u W a b c₁ φ x0r I1 α + expUtil ν G u W a b c₁ φ x0r I2 α) / 2 =
      ∫ p, (u (hedgedPayoff W a b c₁ φ x0r I1 α p.1 p.2) +
        u (hedgedPayoff W a b c₁ φ x0r I2 α p.1 p.2)) / 2 ∂(ν.prod G) := by
    unfold expUtil
    rw [integral_div, integral_add i1 i2]
  rw [hlhs]
  unfold expUtil
  have hpt := fun p : ℝ × ℝ => pt_strict u hu W a b c₁ φ x0r α p.1 p.2 I1 I2 hstd.b_pos
    hstd.c₁_pos hstd.c₁b_lt_one h12
  have iavg : Integrable (fun p : ℝ × ℝ => (u (hedgedPayoff W a b c₁ φ x0r I1 α p.1 p.2) +
      u (hedgedPayoff W a b c₁ φ x0r I2 α p.1 p.2)) / 2) (ν.prod G) := (i1.add i2).div_const 2
  have hd : 0 < ∫ p, (u (hedgedPayoff W a b c₁ φ x0r ((I1 + I2) / 2) α p.1 p.2) -
      (u (hedgedPayoff W a b c₁ φ x0r I1 α p.1 p.2) +
        u (hedgedPayoff W a b c₁ φ x0r I2 α p.1 p.2)) / 2) ∂(ν.prod G) := by
    rw [integral_pos_iff_support_of_nonneg (fun p => (sub_pos.mpr (hpt p)).le) (im.sub iavg)]
    have hsupp : Function.support (fun p : ℝ × ℝ =>
        u (hedgedPayoff W a b c₁ φ x0r ((I1 + I2) / 2) α p.1 p.2) -
          (u (hedgedPayoff W a b c₁ φ x0r I1 α p.1 p.2) +
            u (hedgedPayoff W a b c₁ φ x0r I2 α p.1 p.2)) / 2) = Set.univ :=
      Set.eq_univ_of_forall (fun p => Function.mem_support.mpr (sub_pos.mpr (hpt p)).ne')
    rw [hsupp, measure_univ]
    norm_num
  rw [integral_sub im iavg] at hd
  linarith

end HedgeInvP561

open HedgeInvP561 in
open MeasureTheory in
theorem solution (ν G : Measure ℝ) (u : ℝ → ℝ) (W a b c₁ : ℝ)
    (φ : ℝ → ℝ) (x0r αbar : ℝ)
    (hstd : HedgeInv.Order.StandingAssumptions ν G b c₁ φ x0r)
    (hu : HedgeInv.Order.IsDARADAPUtility u)
    (hαbar : HedgeInv.Order.AlphaBarCond G W a b c₁ φ x0r αbar)
    (hreg : HedgeInv.Order.RegularityCond ν G u W a b c₁ φ x0r αbar)
    (Istar : ℝ → ℝ)
    (hIdom : ∀ α ∈ Set.Icc (0 : ℝ) αbar, max a 0 < Istar α)
    (hmax : ∀ α ∈ Set.Icc (0 : ℝ) αbar,
      IsMaxOn (fun I => HedgeInv.Order.expUtil ν G u W a b c₁ φ x0r I α) (Set.Ioi (max a 0))
        (Istar α)) :
    MonotoneOn Istar (Set.Icc (0 : ℝ) αbar) := by
  intro α1 hα1 α2 hα2 h12
  by_contra hlt
  push Not at hlt
  have hJ := hIdom α2 hα2
  have hI := hIdom α1 hα1
  have hid := supermod ν G u W a b c₁ φ x0r αbar hstd hu hαbar hreg hJ hlt.le hα1 hα2 h12
  have m2 := isMaxOn_iff.mp (hmax α2 hα2) (Istar α1) hI
  have m1 := isMaxOn_iff.mp (hmax α1 hα1) (Istar α2) hJ
  have hs := strict_mid ν G u W a b c₁ φ x0r αbar hstd hu hreg hJ hlt hα1
  have m3 := isMaxOn_iff.mp (hmax α1 hα1) ((Istar α2 + Istar α1) / 2)
    (show max a 0 < (Istar α2 + Istar α1) / 2 by linarith)
  linarith
