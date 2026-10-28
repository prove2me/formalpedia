-- Prove2me | solution 1 for InfluencerAuth.Turnover.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:08:02.337617+00:00
-- url     : https://prove2.me/submissions/025ef092-dac2-4f39-9f98-2fedca97d0d0

import Mathlib
import Definitions.Def_InfluencerAuth_Turnover_Model

open MeasureTheory Set

namespace InflP3Aux

theorem ibp {φ φ' q : ℝ → ℝ} {T : ℝ} (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : Continuous φ')
    (hq : IntervalIntegrable q volume 0 T) :
    φ T * (∫ s in (0:ℝ)..T, q s) =
      ∫ t in (0:ℝ)..T, (φ' t * (∫ s in (0:ℝ)..t, q s) + φ t * q t) := by
  have hD : AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in (0:ℝ)..x, q v) 0 T :=
    hq.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hderiv : deriv φ = φ' := funext fun t => (hφ t).deriv
  have hC1 : ContDiff ℝ 1 φ := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun t => (hφ t).differentiableAt, hderiv ▸ hφ'⟩
  have hφAC : AbsolutelyContinuousOnInterval φ 0 T := hC1.contDiffOn.absolutelyContinuousOnInterval
  have key := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hφAC hD
  simp only [intervalIntegral.integral_same, mul_zero, sub_zero] at key
  rw [← key]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hq.ae_hasDerivAt_integral] with x hx hxI
  have hx' : x ∈ uIcc 0 T := uIoc_subset_uIcc hxI
  rw [hderiv, (hx hx' 0 (by simp)).deriv]

end InflP3Aux

namespace InflP3Aux
open InfluencerAuth.Switch InfluencerAuth.Turnover Filter Topology

theorem ff_meas (γ : ℝ) {S : Set ℝ} (hS : MeasurableSet S) : Measurable (followerFactor γ S) := by
  unfold followerFactor; exact Measurable.ite hS measurable_const measurable_const

theorem pf_meas (γ φ : ℝ) {S : Set ℝ} (hS : MeasurableSet S) : Measurable (profitFactor γ φ S) := by
  unfold profitFactor; exact Measurable.ite hS measurable_const measurable_const

/-- The always-authentic awareness path (logistic). -/
noncomputable def Abar (β x A0 : ℝ) (t : ℝ) : ℝ :=
  (β / (β - x) + ((1 - A0 * (β / (β - x))) / A0) * Real.exp (-(β - x) * t))⁻¹

theorem Abar_props (β x A0 : ℝ) (hβ : 0 < β) (hx : 0 < x) (hxβ : x < β) (hA0 : 0 < A0)
    (hA0' : A0 < (β - x) / β) :
    (∀ t, HasDerivAt (Abar β x A0) (β * Abar β x A0 t * (1 - Abar β x A0 t) - x * Abar β x A0 t) t)
    ∧ (∀ t, 0 < Abar β x A0 t) ∧ (∀ t, β * Abar β x A0 t ≤ β - x) ∧ Abar β x A0 0 = A0 := by
  have hk : 0 < β - x := by linarith
  have hkc : (β - x) * (β / (β - x)) = β := by field_simp
  have hc0pos : 0 < β / (β - x) := div_pos hβ hk
  have hmpos : 0 < (1 - A0 * (β / (β - x))) / A0 := by
    apply div_pos _ hA0
    have : A0 * β < β - x := by rw [lt_div_iff₀ hβ] at hA0'; linarith
    rw [mul_div_assoc', sub_pos, div_lt_one hk]; exact this
  unfold Abar
  generalize hm : (1 - A0 * (β / (β - x))) / A0 = m at *
  have hA0m : A0 * (β / (β - x) + m) = 1 := by rw [← hm]; field_simp; ring
  generalize β / (β - x) = c0 at *
  have hy : ∀ t, 0 < c0 + m * Real.exp (-(β - x) * t) := fun t => by positivity
  refine ⟨fun t => ?_, fun t => inv_pos.2 (hy t), fun t => ?_, ?_⟩
  · have h1 : HasDerivAt (fun t => c0 + m * Real.exp (-(β - x) * t))
        (m * (Real.exp (-(β - x) * t) * (-(β - x)))) t := by
      have := ((hasDerivAt_id t).const_mul (-(β - x))).exp.const_mul m
      simpa using this.const_add c0
    have h2 := h1.inv (hy t).ne'
    have h3 : HasDerivAt (fun t => (c0 + m * Real.exp (-(β - x) * t))⁻¹) _ t := h2
    refine h3.congr_deriv ?_
    have hyt := (hy t).ne'
    field_simp
    linear_combination (-1 : ℝ) * hkc
  · rw [mul_inv_le_iff₀ (hy t)]
    nlinarith [mul_pos hmpos (Real.exp_pos (-(β - x) * t))]
  · simp only [mul_zero, Real.exp_zero, mul_one]
    rw [inv_eq_iff_eq_inv]; exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hA0m))

theorem ff_bounds (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (S : Set ℝ) (t : ℝ) :
    γ ≤ followerFactor γ S t ∧ followerFactor γ S t ≤ 1 := by
  unfold followerFactor; split_ifs <;> constructor <;> linarith

theorem integrable_profit (γ φ r : ℝ) (hr : 0 < r) (hγφ : 1 < γ * φ) {S : Set ℝ}
    (hS : MeasurableSet S) (a : ℝ → ℝ) (ha : Continuous a) (hab : ∀ t, 0 ≤ t → a t ∈ Icc (0:ℝ) 1) :
    IntegrableOn (fun t => Real.exp (-r * t) * profitFactor γ φ S t * a t) (Ioi 0) := by
  refine Integrable.mono' (Integrable.const_mul (exp_neg_integrableOn_Ioi 0 hr) (γ * φ)) ?_ ?_
  · exact (((by fun_prop : Continuous fun t => Real.exp (-r * t)).measurable.mul
      (pf_meas γ φ hS)).mul ha.measurable).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have h1 := hab t (le_of_lt ht)
    have hp : |profitFactor γ φ S t| ≤ γ * φ := by
      unfold profitFactor; split_ifs <;> rw [abs_of_pos (by linarith)] <;> linarith
    have hp0 : 0 ≤ |profitFactor γ φ S t| := abs_nonneg _
    have ha1 : |a t| ≤ 1 := abs_le.2 ⟨by linarith [h1.1], h1.2⟩
    have ha0 : 0 ≤ |a t| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he := Real.exp_pos (-r * t)
    calc Real.exp (-r * t) * |profitFactor γ φ S t| * |a t|
        ≤ Real.exp (-r * t) * (γ * φ) * 1 := by gcongr
      _ = γ * φ * Real.exp (-r * t) := by ring

theorem ii_h (β γ x : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) {S : Set ℝ} (hS : MeasurableSet S)
    (a : ℝ → ℝ) (ha : Continuous a) (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun s => β * followerFactor γ S s * a s * (1 - a s) - x * a s) volume 0 T := by
  have hff : IntervalIntegrable (followerFactor γ S) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      (ff_meas γ hS).aestronglyMeasurable ?_
    exact Eventually.of_forall fun t => by
      have := ff_bounds γ hγ0 hγ1 S t
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have h2 := hff.continuousOn_mul (g := fun s => β * a s * (1 - a s)) (by fun_prop)
  have h3 := h2.sub ((by fun_prop : Continuous fun s => x * a s).intervalIntegrable 0 T)
  have e : (fun s => β * followerFactor γ S s * a s * (1 - a s) - x * a s) =
      fun s => β * a s * (1 - a s) * followerFactor γ S s - x * a s := by
    funext s; ring
  rw [e]; exact h3

theorem core (γ φ β r x A0 : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hβ : 0 < β)
    (hr : 0 < r) (hγφ : 1 < γ * φ) (hx : 0 < x) (hxβ : x < β) (hC2 : Condition2 γ φ β r x)
    (hA0 : 0 < A0) (hA0' : A0 < (β - x) / β)
    (S : Set ℝ) (hS : MeasurableSet S) (a : ℝ → ℝ) (ha : Continuous a)
    (hab : ∀ t, 0 ≤ t → a t ∈ Icc (0:ℝ) 1)
    (hai : ∀ t, 0 ≤ t → a t = A0 + ∫ s in (0:ℝ)..t,
      (β * followerFactor γ S s * a s * (1 - a s) - x * a s)) :
    discountedProfit γ φ r S a ≤ discountedProfit γ φ r ∅ (Abar β x A0) := by
  obtain ⟨hAd, hApos, hAle, hA00⟩ := Abar_props β x A0 hβ hx hxβ hA0 hA0'
  generalize Abar β x A0 = ab at *
  have hAc : Continuous ab := continuous_iff_continuousAt.2 fun t => (hAd t).continuousAt
  have hk : 0 < β - x := by linarith
  have hab1 : ∀ t, ab t ≤ 1 := fun t => by
    have := hAle t
    by_contra hc; have hc' := lt_of_not_ge hc; nlinarith
  have hAi : ∀ t, ab t = A0 + ∫ s in (0:ℝ)..t, (β * ab s * (1 - ab s) - x * ab s) := by
    intro t
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hAd s)
      ((by fun_prop : Continuous fun s => β * ab s * (1 - ab s) - x * ab s).intervalIntegrable _ _),
      hA00]
    ring
  obtain ⟨q, hq⟩ : ∃ q : ℝ → ℝ, q = fun s => (β * ab s * (1 - ab s) - x * ab s) -
      (β * followerFactor γ S s * a s * (1 - a s) - x * a s) := ⟨_, rfl⟩
  have hqi : ∀ T, 0 ≤ T → IntervalIntegrable q volume 0 T := by
    intro T hT; rw [hq]
    exact ((by fun_prop : Continuous fun s => β * ab s * (1 - ab s) - x * ab s).intervalIntegrable
      0 T).sub (ii_h β γ x hγ₀ hγ₁ hS a ha T hT)
  have hD : ∀ t, 0 ≤ t → ∫ s in (0:ℝ)..t, q s = ab t - a t := by
    intro t ht
    rw [hq, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun s => β * ab s * (1 - ab s) - x * ab s).intervalIntegrable 0 t)
      (ii_h β γ x hγ₀ hγ₁ hS a ha t ht), hAi t, hai t ht]
    ring
  -- comparison: a ≤ ab
  have hcmp : ∀ T, 0 ≤ T → a T ≤ ab T := by
    intro T hT
    obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, L = fun t => (β - x) - β * (ab t + a t) := ⟨_, rfl⟩
    have hLc : Continuous L := by rw [hL]; fun_prop
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → ℝ, Ψ = fun t => ∫ s in (0:ℝ)..t, L s := ⟨_, rfl⟩
    have hΨd : ∀ t, HasDerivAt Ψ (L t) t := fun t => by
      rw [hΨ]; exact (hLc.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hΨc : Continuous Ψ := continuous_iff_continuousAt.2 fun t => (hΨd t).continuousAt
    have hφd : ∀ t, HasDerivAt (fun t => Real.exp (-Ψ t)) (Real.exp (-Ψ t) * -(L t)) t :=
      fun t => (hΨd t).neg.exp
    have key := ibp (φ := fun t => Real.exp (-Ψ t)) (φ' := fun t => Real.exp (-Ψ t) * -(L t))
      hφd (by fun_prop) (hqi T hT)
    rw [hD T hT] at key
    have hnn : 0 ≤ ∫ t in (0:ℝ)..T,
        (Real.exp (-Ψ t) * -(L t) * (∫ s in (0:ℝ)..t, q s) + Real.exp (-Ψ t) * q t) := by
      apply intervalIntegral.integral_nonneg hT
      intro t ht
      rw [hD t ht.1]
      have hfb := ff_bounds γ hγ₀ hγ₁ S t
      have hat := hab t ht.1
      have e : Real.exp (-Ψ t) * -(L t) * (ab t - a t) + Real.exp (-Ψ t) * q t =
          Real.exp (-Ψ t) * (β * (a t * (1 - a t)) * (1 - followerFactor γ S t)) := by
        rw [hL, hq]; ring
      rw [e]
      apply mul_nonneg (Real.exp_pos _).le
      exact mul_nonneg (mul_nonneg hβ.le (mul_nonneg hat.1 (by linarith [hat.2])))
        (by linarith [hfb.2])
    rw [← key] at hnn
    have := (mul_nonneg_iff_of_pos_left (Real.exp_pos (-Ψ T))).1 hnn
    linarith
  -- Condition 2 in product form
  have hC2' : (γ * φ - 1) * (r + β - x) < (1 - γ) * x := by
    unfold Condition2 at hC2
    exact (lt_div_iff₀ (by linarith)).1 hC2
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 1 / (r + (β - x)) := ⟨_, rfl⟩
  have hlampos : 0 < lam := by rw [hlam]; apply div_pos one_pos; linarith
  have hlam1 : lam * (r + (β - x)) = 1 := by rw [hlam]; field_simp
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun t => Real.exp (-r * t) * profitFactor γ φ ∅ t * ab t -
      Real.exp (-r * t) * profitFactor γ φ S t * a t := ⟨_, rfl⟩
  have hI1 := integrable_profit γ φ r hr hγφ MeasurableSet.empty ab hAc
    (fun t _ => ⟨(hApos t).le, hab1 t⟩)
  have hI2 := integrable_profit γ φ r hr hγφ hS a ha hab
  have hGint : IntegrableOn G (Ioi 0) := by rw [hG]; exact hI1.sub hI2
  have hmain : ∀ T, 0 ≤ T → -(lam * Real.exp (-r * T)) ≤ ∫ t in (0:ℝ)..T, G t := by
    intro T hT
    have hφd : ∀ t, HasDerivAt (fun t => lam * Real.exp (-r * t))
        (lam * (Real.exp (-r * t) * (-r))) t := fun t => by
      have := (((hasDerivAt_id t).const_mul (-r)).exp).const_mul lam
      exact this.congr_deriv (by simp)
    have key := ibp (φ := fun t => lam * Real.exp (-r * t))
      (φ' := fun t => lam * (Real.exp (-r * t) * (-r))) hφd (by fun_prop) (hqi T hT)
    rw [hD T hT] at key
    have hGi : IntervalIntegrable G volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 (hGint.mono_set Ioc_subset_Ioi_self)
    have hRi : IntervalIntegrable (fun t => lam * (Real.exp (-r * t) * (-r)) *
        (∫ s in (0:ℝ)..t, q s) + lam * Real.exp (-r * t) * q t) volume 0 T := by
      apply IntervalIntegrable.add
      · apply ContinuousOn.intervalIntegrable
        have : ContinuousOn (fun t => lam * (Real.exp (-r * t) * (-r)) * (ab t - a t)) (uIcc 0 T) :=
          (by fun_prop : Continuous _).continuousOn
        refine this.congr fun t ht => ?_
        rw [uIcc_of_le hT] at ht
        simp only [hD t ht.1]
      · exact (hqi T hT).continuousOn_mul (g := fun t => lam * Real.exp (-r * t))
          (by fun_prop)
    have hsum : 0 ≤ ∫ t in (0:ℝ)..T, (G t + (lam * (Real.exp (-r * t) * (-r)) *
        (∫ s in (0:ℝ)..t, q s) + lam * Real.exp (-r * t) * q t)) := by
      apply intervalIntegral.integral_nonneg hT
      intro t ht
      rw [hD t ht.1]
      have hat := hab t ht.1
      have hc := hcmp t ht.1
      have hAl := hAle t
      have hpf0 : profitFactor γ φ ∅ t = 1 := by simp [profitFactor]
      have he := Real.exp_pos (-r * t)
      have e : G t + (lam * (Real.exp (-r * t) * (-r)) * (ab t - a t) + lam * Real.exp (-r * t) * q t)
          = Real.exp (-r * t) * lam * ((r + (β - x)) * (ab t - profitFactor γ φ S t * a t)
              - r * (ab t - a t) + q t) := by
        rw [hG]; simp only [hpf0]
        linear_combination (Real.exp (-r * t) * (ab t - profitFactor γ φ S t * a t)) * hlam1.symm
      rw [e]
      apply mul_nonneg (mul_nonneg he.le hlampos.le)
      rw [hq]
      have hba : β * a t ≤ β * ab t := by nlinarith
      have h1 : 0 ≤ (ab t - a t) * (2 * (β - x) - β * (ab t + a t)) :=
        mul_nonneg (by linarith) (by linarith)
      by_cases hs : t ∈ S
      · have hff : followerFactor γ S t = γ := by simp [followerFactor, hs]
        have hpf : profitFactor γ φ S t = γ * φ := by simp [profitFactor, hs]
        simp only [hff, hpf]
        have h2 : 0 ≤ a t * ((1 - γ) * (β * (1 - a t)) - (r + (β - x)) * (γ * φ - 1)) := by
          apply mul_nonneg hat.1
          have : x ≤ β * (1 - a t) := by linarith
          nlinarith
        nlinarith
      · have hff : followerFactor γ S t = 1 := by simp [followerFactor, hs]
        have hpf : profitFactor γ φ S t = 1 := by simp [profitFactor, hs]
        simp only [hff, hpf]
        nlinarith
    rw [intervalIntegral.integral_add hGi hRi, ← key] at hsum
    have h1 : ab T - a T ≤ 1 := by linarith [(hab T hT).1, hab1 T]
    have h2 : 0 ≤ ab T - a T := by linarith [hcmp T hT]
    have h3 : 0 ≤ lam * Real.exp (-r * T) := by positivity
    nlinarith
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hGint tendsto_id
  have hlow : Tendsto (fun T => -(lam * Real.exp (-r * T))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 hr))).const_mul lam
    simpa using this.neg
  have h0 : 0 ≤ ∫ t in Ioi 0, G t :=
    le_of_tendsto_of_tendsto hlow hlim (eventually_atTop.2 ⟨0, hmain⟩)
  unfold discountedProfit
  rw [hG, integral_sub hI1 hI2] at h0
  linarith

end InflP3Aux

open InfluencerAuth.Switch InfluencerAuth.Turnover

theorem solution (γ φ β r x : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hφ : 1 < φ) (hβ : 0 < β)
    (hr : 0 < r) (hγφ : 1 < γ * φ) (hx : 0 < x) (hxβ : x < β)
    (hC2 : Condition2 γ φ β r x) :
    ∀ A₀ ∈ Set.Ioo (0 : ℝ) ((β - x) / β), ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r x A₀ ∅ A := by
  intro A0 hA0
  obtain ⟨hA0p, hA0'⟩ := hA0
  obtain ⟨hAd, hApos, hAle, hA00⟩ := InflP3Aux.Abar_props β x A0 hβ hx hxβ hA0p hA0'
  have hAc : Continuous (InflP3Aux.Abar β x A0) :=
    continuous_iff_continuousAt.2 fun t => (hAd t).continuousAt
  refine ⟨InflP3Aux.Abar β x A0, MeasurableSet.empty,
    ⟨hAc.continuousOn, hA00, fun t _ => ⟨(hApos t).le, ?_⟩, fun t _ => ?_⟩, ?_⟩
  · have := hAle t
    by_contra hc
    have hc' := lt_of_not_ge hc
    nlinarith
  · have e : (fun s => β * followerFactor γ ∅ s * InflP3Aux.Abar β x A0 s *
        (1 - InflP3Aux.Abar β x A0 s) - x * InflP3Aux.Abar β x A0 s) =
        fun s => β * InflP3Aux.Abar β x A0 s * (1 - InflP3Aux.Abar β x A0 s) -
          x * InflP3Aux.Abar β x A0 s := by
      funext s; simp [followerFactor]
    rw [e, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hAd s)
      ((by fun_prop : Continuous fun s => β * InflP3Aux.Abar β x A0 s *
        (1 - InflP3Aux.Abar β x A0 s) - x * InflP3Aux.Abar β x A0 s).intervalIntegrable _ _), hA00]
    ring
  · intro S' A' hS' hp
    obtain ⟨hc, h0, hb, hi⟩ := hp
    have hc' : Continuous (fun t => A' (max t 0)) :=
      hc.comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 0)
    have heq : ∀ t, 0 ≤ t → A' (max t 0) = A' t := fun t ht => by rw [max_eq_left ht]
    have hdp : discountedProfit γ φ r S' A' = discountedProfit γ φ r S' (fun t => A' (max t 0)) := by
      unfold discountedProfit
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      simp only [heq t (le_of_lt ht)]
    rw [hdp]
    refine InflP3Aux.core γ φ β r x A0 hγ₀ hγ₁ hβ hr hγφ hx hxβ hC2 hA0p hA0' S' hS' _ hc'
      (fun t ht => by simp only [heq t ht]; exact hb t ht) (fun t ht => ?_)
    simp only [heq t ht]
    rw [hi t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    simp only [heq s hs.1]
