-- Prove2me | solution 1 for HedgeInv.Value.derivative_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:38:49.80848+00:00
-- url     : https://prove2.me/submissions/61daeaad-69a9-4fef-9aa1-bae56b0401aa

import Mathlib
import Definitions.Def_HedgeInv_Value_Model
set_option autoImplicit false
open MeasureTheory Filter Topology

theorem HGV_conc_line (u : ℝ → ℝ) (hu_conc : ConcaveOn ℝ Set.univ u) (x y : ℝ) :
    ConcaveOn ℝ Set.univ (fun a : ℝ => u (x + a * y)) := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  have := hu_conc.2 (Set.mem_univ (x + a * y)) (Set.mem_univ (x + b * y)) hs ht hst
  simp only [smul_eq_mul] at this ⊢
  have e : x + (s * a + t * b) * y = s * (x + a * y) + t * (x + b * y) := by
    linear_combination (-x) * hst
  rw [e]; exact this

theorem HGV_slope_bounds (u : ℝ → ℝ) (hu_conc : ConcaveOn ℝ Set.univ u) (x y δ α : ℝ)
    (hδ : 0 < δ) (hα : |α| < δ) (hα0 : α ≠ 0) :
    (u (x + δ * y) - u x) / δ ≤ (u (x + α * y) - u x) / α ∧
    (u (x + α * y) - u x) / α ≤ (u (x + (-δ) * y) - u x) / (-δ) := by
  have hanti := (HGV_conc_line u hu_conc x y).slope_anti (Set.mem_univ 0)
  have hs : ∀ a : ℝ, slope (fun a : ℝ => u (x + a * y)) 0 a = (u (x + a * y) - u x) / a := by
    intro a; simp [slope_def_field]
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hmem : ∀ a : ℝ, a ≠ 0 → a ∈ (Set.univ \ {0} : Set ℝ) := fun a ha => ⟨Set.mem_univ _, ha⟩
  have h1 := hanti (hmem α hα0) (hmem δ hδ0) (by have := (abs_lt.1 hα).2; linarith)
  have h2 := hanti (hmem (-δ) (by simpa using hδ0)) (hmem α hα0) (by have := (abs_lt.1 hα).1; linarith)
  rw [hs, hs] at h1 h2
  exact ⟨h1, h2⟩

theorem HGV_abs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (x y : Ω → ℝ)
    (hx : Measurable x) (hy : Measurable y) (u : ℝ → ℝ)
    (hu_conc : ConcaveOn ℝ Set.univ u) (hu_diff : Differentiable ℝ u) (δ : ℝ) (hδ : 0 < δ)
    (h1 : Integrable (fun p => u (x p + δ * y p)) P) (h0 : Integrable (fun p => u (x p)) P)
    (h2 : Integrable (fun p => u (x p + (-δ) * y p)) P) :
    Integrable (fun p => deriv u (x p) * y p) P ∧
    HasDerivAt (fun α => ∫ p, u (x p + α * y p) ∂P) (∫ p, deriv u (x p) * y p ∂P) 0 := by
  have hucont : Continuous u := hu_diff.continuous
  set Q : ℝ → Ω → ℝ := fun α p => (u (x p + α * y p) - u (x p)) / α with hQ
  have hQm : ∀ α, Measurable (Q α) := fun α =>
    ((hucont.measurable.comp (hx.add (measurable_const.mul hy))).sub (hucont.measurable.comp hx)).div_const α
  have hQδ : Integrable (Q δ) P := (h1.sub h0).div_const δ
  have hQδ' : Integrable (Q (-δ)) P := (h2.sub h0).div_const (-δ)
  set bd : Ω → ℝ := fun p => |Q δ p| + |Q (-δ) p| with hbd
  have hbdi : Integrable bd P := hQδ.abs.add hQδ'.abs
  have hbound : ∀ α, |α| < δ → α ≠ 0 → ∀ p, ‖Q α p‖ ≤ bd p := by
    intro α hα hα0 p
    obtain ⟨b1, b2⟩ := HGV_slope_bounds u hu_conc (x p) (y p) δ α hδ hα hα0
    simp only [hQ, hbd, Real.norm_eq_abs] at *
    rw [abs_le]
    constructor
    · have := neg_abs_le ((u (x p + δ * y p) - u (x p)) / δ)
      have := abs_nonneg ((u (x p + -δ * y p) - u (x p)) / -δ)
      linarith
    · have := le_abs_self ((u (x p + -δ * y p) - u (x p)) / -δ)
      have := abs_nonneg ((u (x p + δ * y p) - u (x p)) / δ)
      linarith
  have hQi : ∀ α, |α| < δ → α ≠ 0 → Integrable (Q α) P := fun α hα hα0 =>
    Integrable.mono' hbdi (hQm α).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbound α hα hα0))
  -- pointwise derivative
  have hlim : ∀ p, Tendsto (fun α => Q α p) (𝓝[≠] 0) (𝓝 (deriv u (x p) * y p)) := by
    intro p
    have hd : HasDerivAt u (deriv u (x p + 0 * y p)) (x p + 0 * y p) := (hu_diff _).hasDerivAt
    have hin : HasDerivAt (fun a : ℝ => x p + a * y p) (1 * y p) 0 :=
      ((hasDerivAt_id (0:ℝ)).mul_const (y p)).const_add (x p)
    have hc := hd.comp 0 hin
    have hc' : HasDerivAt (fun a : ℝ => u (x p + a * y p)) (deriv u (x p) * y p) 0 :=
      hc.congr_deriv (by simp)
    have := hasDerivAt_iff_tendsto_slope.1 hc'
    refine this.congr (fun α => ?_)
    simp [hQ, slope_def_field]
  -- limit sandwiched
  have hsand : ∀ p, Q δ p ≤ deriv u (x p) * y p ∧ deriv u (x p) * y p ≤ Q (-δ) p := by
    intro p
    have hev : ∀ᶠ α in 𝓝[≠] (0:ℝ), |α| < δ ∧ α ≠ 0 := by
      refine Filter.Eventually.and ?_ self_mem_nhdsWithin
      exact eventually_nhdsWithin_of_eventually_nhds
        (by filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδ] with a ha
            simpa [Real.dist_eq] using ha)
    constructor
    · refine ge_of_tendsto (hlim p) ?_
      filter_upwards [hev] with α hα
      exact (HGV_slope_bounds u hu_conc (x p) (y p) δ α hδ hα.1 hα.2).1
    · refine le_of_tendsto (hlim p) ?_
      filter_upwards [hev] with α hα
      exact (HGV_slope_bounds u hu_conc (x p) (y p) δ α hδ hα.1 hα.2).2
  have hdm : Measurable (fun p => deriv u (x p) * y p) :=
    ((measurable_deriv u).comp hx).mul hy
  have hdi : Integrable (fun p => deriv u (x p) * y p) P := by
    refine Integrable.mono' hbdi hdm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨s1, s2⟩ := hsand p
    simp only [hbd, Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · have := neg_abs_le (Q δ p)
      have := abs_nonneg (Q (-δ) p)
      linarith
    · have := le_abs_self (Q (-δ) p)
      have := abs_nonneg (Q δ p)
      linarith
  refine ⟨hdi, ?_⟩
  rw [hasDerivAt_iff_tendsto_slope]
  have hev : ∀ᶠ α in 𝓝[≠] (0:ℝ), |α| < δ ∧ α ≠ 0 := by
    refine Filter.Eventually.and ?_ self_mem_nhdsWithin
    exact eventually_nhdsWithin_of_eventually_nhds
      (by filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδ] with a ha
          simpa [Real.dist_eq] using ha)
  have hT : Tendsto (fun α => ∫ p, Q α p ∂P) (𝓝[≠] 0) (𝓝 (∫ p, deriv u (x p) * y p ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence bd ?_ ?_ hbdi ?_
    · filter_upwards with α using (hQm α).aestronglyMeasurable
    · filter_upwards [hev] with α hα
      exact Filter.Eventually.of_forall (hbound α hα.1 hα.2)
    · exact Filter.Eventually.of_forall hlim
  refine hT.congr' ?_
  filter_upwards [hev] with α hα
  have hQa := hQi α hα.1 hα.2
  have hα0 : α ≠ 0 := hα.2
  have hsplit : (fun p => u (x p + α * y p)) = fun p => u (x p) + α * Q α p := by
    funext p
    simp only [hQ]
    field_simp
    ring
  have hint : ∫ p, u (x p + α * y p) ∂P = ∫ p, u (x p) ∂P + α * ∫ p, Q α p ∂P := by
    rw [hsplit, integral_add h0 (hQa.const_mul α), integral_const_mul]
  simp only [slope_def_field, zero_add, sub_zero]
  have : ∫ p, u (x p + 0 * y p) ∂P = ∫ p, u (x p) ∂P := by simp
  rw [this, hint]
  field_simp
  ring

theorem HGV_hedged (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r I α s e : ℝ) :
    HedgeInv.Order.hedgedPayoff W a b c₁ φ x0r I α s e =
      HedgeInv.Value.unhedgedPayoff W a b c₁ I s e + α * (x0r - φ s) := by
  simp only [HedgeInv.Order.hedgedPayoff, HedgeInv.Value.unhedgedPayoff]; ring

theorem HGV_main
    (ν G : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure G]
    (W a b c₁ I : ℝ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (x0r : ℝ)
    (u : ℝ → ℝ) (hu_conc : ConcaveOn ℝ Set.univ u) (hu_diff : Differentiable ℝ u)
    (δ : ℝ) (hδ : 0 < δ)
    (hint : ∀ α ∈ ({-δ, 0, δ} : Set ℝ),
      Integrable (fun p : ℝ × ℝ => u (HedgeInv.Order.hedgedPayoff W a b c₁ φ x0r I α p.1 p.2)) (ν.prod G)) :
    Integrable (fun p : ℝ × ℝ => deriv u (HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2) * (x0r - φ p.1)) (ν.prod G) ∧
    HasDerivAt (fun α => HedgeInv.Order.expUtil ν G u W a b c₁ φ x0r I α)
      (∫ p : ℝ × ℝ, deriv u (HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2) * (x0r - φ p.1) ∂(ν.prod G)) 0 := by
  have hx : Measurable (fun p : ℝ × ℝ => HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2) := by
    unfold HedgeInv.Value.unhedgedPayoff
    fun_prop
  have hy : Measurable (fun p : ℝ × ℝ => x0r - φ p.1) := by fun_prop
  have hI : ∀ α ∈ ({-δ, 0, δ} : Set ℝ), Integrable (fun p : ℝ × ℝ =>
      u (HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2 + α * (x0r - φ p.1))) (ν.prod G) := by
    intro α hα
    have := hint α hα
    simpa only [HGV_hedged] using this
  have h1 := hI δ (by simp)
  have h2 := hI (-δ) (by simp)
  have h0 := hI 0 (by simp)
  simp only [zero_mul, add_zero] at h0
  have := HGV_abs (ν.prod G) _ _ hx hy u hu_conc hu_diff δ hδ h1 h0 h2
  refine ⟨this.1, ?_⟩
  have e : (fun α => HedgeInv.Order.expUtil ν G u W a b c₁ φ x0r I α) =
      fun α => ∫ p : ℝ × ℝ, u (HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2 + α * (x0r - φ p.1)) ∂(ν.prod G) := by
    funext α
    simp only [HedgeInv.Order.expUtil, HGV_hedged]
  rw [e]
  exact this.2

theorem solution
    (ν G : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure G]
    (hG_mean : ∫ e, e ∂G = 0) (hG_L2 : MemLp id 2 G)
    (W a b c₁ I : ℝ) (hb : 0 < b) (hI : max a 0 < I) (hc₁ : 0 < c₁) (hc₁b : c₁ * b < 1)
    (φ : ℝ → ℝ) (hφ_mono : Monotone φ) (hφ_meas : Measurable φ) (hφ_int : Integrable φ ν)
    (x0r : ℝ) (h12 : ∫ s, φ s ∂ν = x0r)
    (u : ℝ → ℝ) (hu_conc : ConcaveOn ℝ Set.univ u) (hu_diff : Differentiable ℝ u)
    (δ : ℝ) (hδ : 0 < δ)
    (hint : ∀ α ∈ ({-δ, 0, δ} : Set ℝ),
      Integrable (fun p : ℝ × ℝ => u (HedgeInv.Order.hedgedPayoff W a b c₁ φ x0r I α p.1 p.2)) (ν.prod G)) :
    HasDerivAt (fun α => HedgeInv.Order.expUtil ν G u W a b c₁ φ x0r I α)
      (∫ p : ℝ × ℝ, deriv u (HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2) * (x0r - φ p.1) ∂(ν.prod G)) 0 :=
  (HGV_main ν G W a b c₁ I φ hφ_meas x0r u hu_conc hu_diff δ hδ hint).2

