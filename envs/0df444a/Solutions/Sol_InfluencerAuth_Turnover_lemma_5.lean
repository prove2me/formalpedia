-- Prove2me | solution 1 for InfluencerAuth.Turnover.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:12:49.978053+00:00
-- url     : https://prove2.me/submissions/cf369c0f-ffff-4345-bbc6-46d846ef2db2

import Mathlib
import Definitions.Def_InfluencerAuth_Turnover_Model

open MeasureTheory Set

namespace InflL5Aux

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


open InfluencerAuth.Switch InfluencerAuth.Turnover

noncomputable def Abar (β x A0 : ℝ) (t : ℝ) : ℝ :=
  (β / (β - x) + ((1 - A0 * (β / (β - x))) / A0) * Real.exp (-(β - x) * t))⁻¹

theorem Abar_deriv (β x A0 : ℝ) (hβ : 0 < β) (hxβ : x < β) (hA0 : 0 < A0) (t : ℝ) (ht : 0 ≤ t) :
    0 < β / (β - x) + ((1 - A0 * (β / (β - x))) / A0) * Real.exp (-(β - x) * t) ∧
    HasDerivAt (Abar β x A0) (β * Abar β x A0 t * (1 - Abar β x A0 t) - x * Abar β x A0 t) t := by
  have hk : 0 < β - x := by linarith
  have hkc : (β - x) * (β / (β - x)) = β := by field_simp
  have hc0pos : 0 < β / (β - x) := div_pos hβ hk
  have hm : (1 - A0 * (β / (β - x))) / A0 = 1 / A0 - β / (β - x) := by field_simp
  have hy : 0 < β / (β - x) + ((1 - A0 * (β / (β - x))) / A0) * Real.exp (-(β - x) * t) := by
    rw [hm]
    have he1 : Real.exp (-(β - x) * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he0 := Real.exp_pos (-(β - x) * t)
    have : 0 < 1 / A0 := by positivity
    nlinarith
  refine ⟨hy, ?_⟩
  unfold Abar
  generalize (1 - A0 * (β / (β - x))) / A0 = m at *
  generalize β / (β - x) = c0 at *
  clear hm
  have h1 : HasDerivAt (fun t => c0 + m * Real.exp (-(β - x) * t))
      (m * (Real.exp (-(β - x) * t) * (-(β - x)))) t := by
    have := ((hasDerivAt_id t).const_mul (-(β - x))).exp.const_mul m
    simpa using this.const_add c0
  have h2 := h1.inv hy.ne'
  have h3 : HasDerivAt (fun t => (c0 + m * Real.exp (-(β - x) * t))⁻¹) _ t := h2
  refine h3.congr_deriv ?_
  have hyt := hy.ne'
  have hyt' : c0 + m * Real.exp (-((β - x) * t)) ≠ 0 := by rw [← neg_mul]; exact hy.ne'
  field_simp
  linear_combination (-1 : ℝ) * hkc

end InflL5Aux

open InfluencerAuth.Switch InfluencerAuth.Turnover

theorem solution (γ φ β r x : ℝ) (hβ : 0 < β) (hr : 0 < r) (hx : 0 < x) (hxβ : x < β)
    (A₀ : ℝ) (hA₀ : A₀ ∈ Set.Ioo (0 : ℝ) 1) (A : ℝ → ℝ) (hA : IsPath β γ x A₀ ∅ A) :
    InfluencerAuth.Switch.discountedProfit γ φ r ∅ A = authValue β x r A₀ := by
  obtain ⟨hA0, -⟩ := hA₀
  obtain ⟨hc, h0, hb, hi⟩ := hA
  set B := InflL5Aux.Abar β x A₀ with hB
  have hBd : ∀ t, 0 ≤ t → HasDerivAt B (β * B t * (1 - B t) - x * B t) t :=
    fun t ht => (InflL5Aux.Abar_deriv β x A₀ hβ hxβ hA0 t ht).2
  have hB0 : B 0 = A₀ := by
    rw [hB]; unfold InflL5Aux.Abar
    simp only [mul_zero, Real.exp_zero, mul_one]
    have hk : 0 < β - x := by linarith
    rw [inv_eq_iff_eq_inv]; field_simp; ring
  have hBc : ContinuousOn B (Ici 0) := fun t ht => (hBd t ht).continuousAt.continuousWithinAt
  -- clamped versions
  have hAc' : Continuous (fun t => A (max t 0)) :=
    hc.comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 0)
  have hBc' : Continuous (fun t => B (max t 0)) :=
    hBc.comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 0)
  have hff : ∀ s, followerFactor γ ∅ s = 1 := fun s => by simp [followerFactor]
  -- integral equations, in terms of clamped functions
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun u => β * u * (1 - u) - x * u := ⟨_, rfl⟩
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hBi : ∀ t, 0 ≤ t → B t = A₀ + ∫ s in (0:ℝ)..t, g (B (max s 0)) := by
    intro t ht
    have e : ∫ s in (0:ℝ)..t, g (B (max s 0)) = ∫ s in (0:ℝ)..t, (β * B s * (1 - B s) - x * B s) := by
      apply intervalIntegral.integral_congr
      intro s hs; rw [uIcc_of_le ht] at hs
      simp only [hg, max_eq_left hs.1]
    rw [e, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hBd s (by rw [uIcc_of_le ht] at hs; exact hs.1)), hB0]
    · ring
    · apply ContinuousOn.intervalIntegrable
      have : ContinuousOn (fun s => g (B (max s 0))) (uIcc 0 t) :=
        (hgc.comp hBc').continuousOn
      refine this.congr fun s hs => ?_
      rw [uIcc_of_le ht] at hs
      simp only [hg, max_eq_left hs.1]
  have hAi : ∀ t, 0 ≤ t → A t = A₀ + ∫ s in (0:ℝ)..t, g (A (max s 0)) := by
    intro t ht
    rw [hi t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs; rw [uIcc_of_le ht] at hs
    simp only [hg, hff, max_eq_left hs.1, mul_one]
  obtain ⟨q, hq⟩ : ∃ q : ℝ → ℝ, q = fun s => g (B (max s 0)) - g (A (max s 0)) := ⟨_, rfl⟩
  have hqc : Continuous q := by rw [hq]; exact (hgc.comp hBc').sub (hgc.comp hAc')
  have hD : ∀ t, 0 ≤ t → ∫ s in (0:ℝ)..t, q s = B t - A t := by
    intro t ht
    rw [hq, intervalIntegral.integral_sub
      (show IntervalIntegrable (fun s => g (B (max s 0))) volume 0 t from
        (hgc.comp hBc').intervalIntegrable _ _)
      (show IntervalIntegrable (fun s => g (A (max s 0))) volume 0 t from
        (hgc.comp hAc').intervalIntegrable _ _), hBi t ht, hAi t ht]
    ring
  have heq : ∀ T, 0 ≤ T → A T = B T := by
    intro T hT
    obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, L = fun t => (β - x) - β * (B (max t 0) + A (max t 0)) := ⟨_, rfl⟩
    have hLc : Continuous L := by
      rw [hL]; exact continuous_const.sub (continuous_const.mul (hBc'.add hAc'))
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → ℝ, Ψ = fun t => ∫ s in (0:ℝ)..t, L s := ⟨_, rfl⟩
    have hΨd : ∀ t, HasDerivAt Ψ (L t) t := fun t => by
      rw [hΨ]; exact (hLc.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hΨc : Continuous Ψ := continuous_iff_continuousAt.2 fun t => (hΨd t).continuousAt
    have hφd : ∀ t, HasDerivAt (fun t => Real.exp (-Ψ t)) (Real.exp (-Ψ t) * -(L t)) t :=
      fun t => (hΨd t).neg.exp
    have key := InflL5Aux.ibp (φ := fun t => Real.exp (-Ψ t))
      (φ' := fun t => Real.exp (-Ψ t) * -(L t)) hφd (by fun_prop) (hqc.intervalIntegrable 0 T)
    rw [hD T hT] at key
    have hz : ∫ t in (0:ℝ)..T,
        (Real.exp (-Ψ t) * -(L t) * (∫ s in (0:ℝ)..t, q s) + Real.exp (-Ψ t) * q t) =
        ∫ t in (0:ℝ)..T, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hT] at ht
      simp only
      rw [hD t ht.1, hL, hq, hg]
      simp only [max_eq_left ht.1]
      ring
    rw [hz, intervalIntegral.integral_zero] at key
    have := (mul_eq_zero.1 key).resolve_left (Real.exp_pos _).ne'
    linarith
  unfold discountedProfit authValue
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [heq t (le_of_lt ht), hB, profitFactor, Set.mem_empty_iff_false, if_false, mul_one]
  unfold InflL5Aux.Abar
  exact (div_eq_mul_inv _ _).symm
