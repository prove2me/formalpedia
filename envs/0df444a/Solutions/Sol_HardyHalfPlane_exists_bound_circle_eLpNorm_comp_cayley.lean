-- Prove2me | solution 1 for HardyHalfPlane.exists_bound_circle_eLpNorm_comp_cayley
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T20:13:02.408481+00:00
-- url     : https://prove2.me/submissions/1996919d-a2cf-49df-b24e-f67373153934

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace Sol_HardyHalfPlane_exists_bound_circle_eLpNorm_comp_cayley

open Complex HardyHalfPlane Metric

/-- Sub-mean value property of `‖f‖ ^ q` on circles (`q > 0`), via Jensen's formula and
Jensen's inequality. -/
lemma norm_rpow_le_circleAverage (f : ℂ → ℂ) (c : ℂ) (R q : ℝ) (hR : 0 < R) (hq : 0 < q)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) :
    ‖f c‖ ^ q ≤ Real.circleAverage (fun z => ‖f z‖ ^ q) c R := by
  by_cases h0 : f c = 0
  · rw [h0, norm_zero, Real.zero_rpow hq.ne']
    exact Real.circleAverage_nonneg_of_nonneg (fun x _ => by positivity)
  have habs : |R| = R := abs_of_pos hR
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rwa [habs]
  have hJ := hf'.circleAverage_log_norm hR.ne' h0
  have hsum : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor f (closedBall c |R|) u : ℤ) : ℝ) *
      Real.log (R * ‖c - u‖⁻¹) := by
    apply finsum_nonneg; intro u
    by_cases hu : u ∈ closedBall c |R|
    · by_cases huc : u = c
      · subst huc; simp
      · apply mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf' u)
        apply Real.log_nonneg
        have h1 : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
        have h2 : ‖c - u‖ ≤ R := by
          rw [mem_closedBall, dist_comm, dist_eq_norm, habs] at hu; exact hu
        rw [← div_eq_mul_inv, le_div_iff₀ h1, one_mul]; exact h2
    · simp [hu]
  have hlog : Real.log ‖f c‖ ≤ Real.circleAverage (fun z => Real.log ‖f z‖) c R := by
    rw [hJ]; linarith
  have hcont : ContinuousOn f (closedBall c R) := hf.continuousOn
  have hcm : Continuous (fun θ : ℝ => f (circleMap c R θ)) := by
    refine hcont.comp_continuous (continuous_circleMap c R) (fun θ => ?_)
    exact sphere_subset_closedBall (by simpa [habs] using circleMap_mem_sphere' c R θ)
  -- integrability of `log ‖f‖` on the circle
  have hli : CircleIntegrable (fun z => Real.log ‖f z‖) c R :=
    (hf'.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  -- the function `exp (q log ‖f‖)` agrees with `‖f‖ ^ q` off the zeros
  have hcod : (fun z => Real.exp (q * Real.log ‖f z‖)) =ᶠ[codiscreteWithin (sphere c |R|)]
      (fun z => ‖f z‖ ^ q) := by
    have h1 : f ⁻¹' {0}ᶜ ∈ codiscreteWithin (closedBall c |R|) :=
      hf'.preimage_zero_mem_codiscreteWithin h0 (by simp)
        (isConnected_closedBall (abs_nonneg R))
    have h2 := codiscreteWithin_mono sphere_subset_closedBall h1
    filter_upwards [h2] with z hz
    have hz' : f z ≠ 0 := hz
    rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz'), mul_comm]
  -- Jensen's inequality
  have hjen : Real.exp (Real.circleAverage (fun z => q * Real.log ‖f z‖) c R) ≤
      Real.circleAverage (fun z => Real.exp (q * Real.log ‖f z‖)) c R := by
    rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
    have hpi : (0:ℝ) ≤ 2 * Real.pi := by positivity
    have hI : IntegrableOn (fun θ : ℝ => q * Real.log ‖f (circleMap c R θ)‖) (Set.uIoc 0 (2 * Real.pi)) :=
      by
        have := (hli.const_mul q)
        rw [Set.uIoc_of_le hpi]
        exact this.1
    have hE : IntegrableOn (fun θ : ℝ => Real.exp (q * Real.log ‖f (circleMap c R θ)‖))
        (Set.uIoc 0 (2 * Real.pi)) := by
      have hb : IntegrableOn (fun θ : ℝ => ‖f (circleMap c R θ)‖ ^ q + 1) (Set.uIoc 0 (2 * Real.pi)) := by
        rw [Set.uIoc_of_le hpi]
        exact ((hcm.norm.rpow_const (fun _ => Or.inr hq.le)).add continuous_const).integrableOn_Icc.mono_set
          Set.Ioc_subset_Icc_self
      refine hb.mono' ?_ ?_
      · exact (Real.continuous_exp.measurable.comp
          ((Real.measurable_log.comp hcm.norm.measurable).const_mul q)).aestronglyMeasurable
      · refine Eventually.of_forall (fun θ => ?_)
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        by_cases hz : f (circleMap c R θ) = 0
        · rw [hz, norm_zero, Real.log_zero, mul_zero, Real.exp_zero, Real.zero_rpow hq.ne']
          norm_num
        · rw [mul_comm, ← Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
          linarith
    have := ConvexOn.map_set_average_le (μ := volume) (t := Set.uIoc 0 (2 * Real.pi))
      (s := Set.univ) (g := Real.exp) convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
      (by rw [Set.uIoc_of_le hpi, Real.volume_Ioc]; simp [Real.pi_pos])
      (by rw [Set.uIoc_of_le hpi, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (Eventually.of_forall (fun _ => Set.mem_univ _)) hI hE
    exact this
  calc ‖f c‖ ^ q = Real.exp (q * Real.log ‖f c‖) := by
        rw [Real.rpow_def_of_pos (norm_pos_iff.mpr h0), mul_comm]
    _ ≤ Real.exp (Real.circleAverage (fun z => q * Real.log ‖f z‖) c R) := by
        apply Real.exp_le_exp.mpr
        have := Real.circleAverage_fun_smul (a := q) (f := fun z => Real.log ‖f z‖) (c := c) (R := R)
        simp only [smul_eq_mul] at this
        rw [this]
        exact mul_le_mul_of_nonneg_left hlog hq.le
    _ ≤ Real.circleAverage (fun z => Real.exp (q * Real.log ‖f z‖)) c R := hjen
    _ = Real.circleAverage (fun z => ‖f z‖ ^ q) c R :=
        Real.circleAverage_congr_codiscreteWithin hcod hR.ne'


lemma ofReal_norm_rpow (x : ℂ) (q : ℝ) (hq : 0 ≤ q) :
    ENNReal.ofReal (‖x‖ ^ q) = ‖x‖ₑ ^ q := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq, ofReal_norm]

lemma circ_eq' (s : ℂ) (ρ θ : ℝ) :
    s + (ρ : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) = circleMap s ρ θ := by
  simp [circleMap, Complex.exp_mul_I]

lemma polar_norm (p : ℝ × ℝ) (hp : 0 < p.1) :
    ‖(p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I)‖ = p.1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le]
  have : ‖(Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I‖ = 1 := by
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
    exact Complex.norm_exp_ofReal_mul_I p.2
  rw [this, mul_one]

/-- Lower bound for the circle integral of `‖Ψ‖ ^ q` over `(-π, π)`. -/
lemma circle_lower (Ψ : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hΨd : DifferentiableOn ℂ Ψ U)
    (s : ℂ) (ρ q : ℝ) (hρ : 0 < ρ) (hq : 0 < q) (hsub : closedBall s ρ ⊆ U) :
    ENNReal.ofReal (2 * Real.pi * ‖Ψ s‖ ^ q) ≤
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ‖Ψ (circleMap s ρ θ)‖ₑ ^ q := by
  have han : AnalyticOnNhd ℂ Ψ (closedBall s ρ) := (hΨd.analyticOnNhd hU).mono hsub
  have hS := norm_rpow_le_circleAverage Ψ s ρ q hρ hq han
  rw [Real.circleAverage_def, smul_eq_mul] at hS
  set g : ℝ → ℝ := fun θ => ‖Ψ (circleMap s ρ θ)‖ ^ q with hg
  have hgc : Continuous g := by
    have : Continuous (fun θ : ℝ => Ψ (circleMap s ρ θ)) := by
      refine (hΨd.continuousOn.mono hsub).comp_continuous (continuous_circleMap s ρ) (fun θ => ?_)
      exact sphere_subset_closedBall (by simpa [abs_of_pos hρ] using circleMap_mem_sphere' s ρ θ)
    exact this.norm.rpow_const (fun _ => Or.inr hq.le)
  have hper : Function.Periodic g (2 * Real.pi) := by
    intro θ; simp only [hg]; rw [periodic_circleMap s ρ θ]
  have hshift := hper.intervalIntegral_add_eq 0 (-Real.pi)
  rw [show (0:ℝ) + 2 * Real.pi = 2 * Real.pi by ring,
    show -Real.pi + 2 * Real.pi = Real.pi by ring] at hshift
  have hpi : 0 < 2 * Real.pi := by positivity
  have h2 : 2 * Real.pi * ‖Ψ s‖ ^ q ≤ ∫ θ in (-Real.pi)..Real.pi, g θ := by
    have h3 : ∫ θ in (0:ℝ)..2 * Real.pi, ‖Ψ (circleMap s ρ θ)‖ ^ q = ∫ θ in (0:ℝ)..2 * Real.pi, g θ :=
      rfl
    rw [h3, hshift] at hS
    have := mul_le_mul_of_nonneg_left hS hpi.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at this
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo] at h2
  have hint : IntegrableOn g (Set.Ioo (-Real.pi) Real.pi) :=
    (hgc.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  calc ENNReal.ofReal (2 * Real.pi * ‖Ψ s‖ ^ q) ≤ ENNReal.ofReal (∫ θ in Set.Ioo (-Real.pi) Real.pi, g θ) :=
        ENNReal.ofReal_le_ofReal h2
    _ = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (g θ) :=
        ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun θ => by positivity))
    _ = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ‖Ψ (circleMap s ρ θ)‖ₑ ^ q := by
        congr 1; funext θ; exact ofReal_norm_rpow _ q hq.le

/-- Sub-mean value property of `‖Ψ‖ ^ q` on discs. -/
lemma disc_mean (Ψ : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hΨd : DifferentiableOn ℂ Ψ U)
    (hΨm : Measurable Ψ) (s : ℂ) (R q : ℝ) (hR : 0 < R) (hq : 0 < q) (hsub : closedBall s R ⊆ U) :
    ENNReal.ofReal (Real.pi * R ^ 2 * ‖Ψ s‖ ^ q) ≤ ∫⁻ w in ball s R, ‖Ψ w‖ₑ ^ q := by
  set A := ‖Ψ s‖ ^ q with hA_def
  have hA : 0 ≤ A := by positivity
  set F : ℂ → ℝ≥0∞ := (ball (0:ℂ) R).indicator (fun w => ‖Ψ (s + w)‖ₑ ^ q) with hF
  have hFm : Measurable F :=
    ((hΨm.comp (measurable_const.add measurable_id)).enorm.pow_const q).indicator
      measurableSet_ball
  have step1 : ∫⁻ w in ball s R, ‖Ψ w‖ₑ ^ q = ∫⁻ w, F w := by
    rw [← lintegral_indicator measurableSet_ball,
      ← lintegral_add_left_eq_self _ s]
    congr 1; funext w
    simp only [hF, Set.indicator, Metric.mem_ball, dist_zero_right, dist_self_add_left]
  have hcm : Continuous (fun p : ℝ × ℝ => circleMap s p.1 p.2) := by
    unfold circleMap; fun_prop
  set G : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * ‖Ψ (circleMap s p.1 p.2)‖ₑ ^ q with hG
  have hGm : Measurable G := by
    simp only [hG]
    refine (ENNReal.measurable_ofReal.comp measurable_fst).mul ?_
    exact (hΨm.comp hcm.measurable).enorm.pow_const q
  have step2 : ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p ≤ ∫⁻ w, F w := by
    rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
    calc ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p
        = ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p) := by
          refine setLIntegral_congr_fun
            (measurableSet_Ioo.prod measurableSet_Ioo) (fun p hp => ?_)
          have hp1 : 0 < p.1 := hp.1.1
          have hpR : p.1 < R := hp.1.2
          simp only [hG, hF, Complex.polarCoord_symm_apply, smul_eq_mul]
          rw [Set.indicator_of_mem]
          · rw [circ_eq']
          rw [Metric.mem_ball, dist_zero_right, polar_norm p hp1]
          exact hpR
      _ ≤ _ := lintegral_mono_set (Set.prod_mono Set.Ioo_subset_Ioi_self subset_rfl)
  have step3 : ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p =
      ∫⁻ ρ in Set.Ioo 0 R, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, G (ρ, θ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hGm.aemeasurable]
  have step4 : ∀ ρ ∈ Set.Ioo 0 R, ENNReal.ofReal (2 * Real.pi * A) * ENNReal.ofReal ρ ≤
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, G (ρ, θ) := by
    intro ρ hρ
    have hm : Measurable (fun θ : ℝ => ‖Ψ (circleMap s ρ θ)‖ₑ ^ q) :=
      (hΨm.comp (continuous_circleMap s ρ).measurable).enorm.pow_const q
    simp only [hG]
    rw [lintegral_const_mul _ hm, mul_comm]
    gcongr
    exact circle_lower Ψ U hU hΨd s ρ q hρ.1 hq
      ((closedBall_subset_closedBall hρ.2.le).trans hsub)
  have step5 : ∫⁻ ρ in Set.Ioo 0 R, ENNReal.ofReal ρ = ENNReal.ofReal (R ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le, integral_id]
      ring
    · exact (continuous_id.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun ρ hρ => hρ.1.le)
  calc ENNReal.ofReal (Real.pi * R ^ 2 * A)
      = ENNReal.ofReal (2 * Real.pi * A) * ENNReal.ofReal (R ^ 2 / 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    _ = ∫⁻ ρ in Set.Ioo 0 R, ENNReal.ofReal (2 * Real.pi * A) * ENNReal.ofReal ρ := by
        rw [lintegral_const_mul _ ENNReal.measurable_ofReal, step5]
    _ ≤ ∫⁻ ρ in Set.Ioo 0 R, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, G (ρ, θ) :=
        setLIntegral_mono' measurableSet_Ioo step4
    _ = ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p := step3.symm
    _ ≤ ∫⁻ w, F w := step2
    _ = ∫⁻ w in ball s R, ‖Ψ w‖ₑ ^ q := step1.symm


lemma sin_half_case (α c : ℝ) (hα1 : -(2 * Real.pi) < α) (hα2 : α < 2 * Real.pi)
    (hs : |Real.sin (α / 2)| < c) :
    |α| < Real.pi * c ∨ 2 * Real.pi - Real.pi * c < |α| := by
  set β := |α| / 2 with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβπ : β < Real.pi := by
    rw [hβ]; have := abs_lt.mpr ⟨hα1, hα2⟩; linarith
  have hsβ : |Real.sin (α / 2)| = Real.sin β := by
    have hsn : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi hβ0 hβπ.le
    rcases le_or_gt 0 α with h | h
    · rw [hβ, abs_of_nonneg h, abs_of_nonneg]
      rw [hβ, abs_of_nonneg h] at hsn; exact hsn
    · rw [hβ, abs_of_neg h, show -α / 2 = -(α / 2) by ring, Real.sin_neg]
      rw [hβ, abs_of_neg h, show -α / 2 = -(α / 2) by ring, Real.sin_neg] at hsn
      rw [abs_of_nonpos (by linarith)]
  rw [hsβ] at hs
  have hpi := Real.pi_pos
  rcases le_or_gt β (Real.pi / 2) with h | h
  · left
    have := Real.mul_le_sin hβ0 h
    have h2 : 2 / Real.pi * β < c := lt_of_le_of_lt this hs
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at h2
    rw [hβ] at h2; linarith
  · right
    have h1 : 0 ≤ Real.pi - β := by linarith
    have h2 : Real.pi - β ≤ Real.pi / 2 := by linarith
    have := Real.mul_le_sin h1 h2
    rw [Real.sin_pi_sub] at this
    have h3 : 2 / Real.pi * (Real.pi - β) < c := lt_of_le_of_lt this hs
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at h3
    rw [hβ] at h3; linarith

lemma norm_circleMap_sub (r θ θ0 : ℝ) (hr : 0 < r) :
    ‖circleMap 0 r θ - circleMap 0 r θ0‖ = r * |2 * Real.sin ((θ - θ0) / 2)| := by
  have h : circleMap 0 r θ - circleMap 0 r θ0 =
      (r * Complex.exp (θ0 * I)) * (Complex.exp (I * ((θ - θ0 : ℝ) : ℂ)) - 1) := by
    simp only [circleMap, zero_add]
    rw [mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
    congr 3
    push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr.le, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs]

/-- Arc estimate: the set of `θ ∈ (0, 2π]` with `r e^{iθ}` in a disc of radius `η` has measure
at most `4πη/r`. -/
lemma arc_measure (r η : ℝ) (hr : 0 < r) (ζ : ℂ) :
    volume ({θ : ℝ | ‖circleMap 0 r θ - ζ‖ < η} ∩ Set.Ioc 0 (2 * Real.pi)) ≤
      ENNReal.ofReal (4 * Real.pi * (η / r)) := by
  set E := {θ : ℝ | ‖circleMap 0 r θ - ζ‖ < η} ∩ Set.Ioc 0 (2 * Real.pi) with hE
  rcases E.eq_empty_or_nonempty with h0 | ⟨θ0, hθ0, hθ0I⟩
  · rw [h0, measure_empty]; simp
  set c := η / r with hc
  have hpi := Real.pi_pos
  have hsub : E ⊆ Set.Ioo (θ0 - Real.pi * c) (θ0 + Real.pi * c) ∪ Set.Ioo 0 (Real.pi * c) ∪
      Set.Ioc (2 * Real.pi - Real.pi * c) (2 * Real.pi) := by
    intro θ ⟨hθ, hθI⟩
    have hθ' : ‖circleMap 0 r θ - ζ‖ < η := hθ
    have hθ0' : ‖circleMap 0 r θ0 - ζ‖ < η := hθ0
    have hd : ‖circleMap 0 r θ - circleMap 0 r θ0‖ < 2 * η := by
      calc ‖circleMap 0 r θ - circleMap 0 r θ0‖
          = ‖(circleMap 0 r θ - ζ) - (circleMap 0 r θ0 - ζ)‖ := by ring_nf
        _ ≤ ‖circleMap 0 r θ - ζ‖ + ‖circleMap 0 r θ0 - ζ‖ := norm_sub_le _ _
        _ < 2 * η := by linarith
    rw [norm_circleMap_sub r θ θ0 hr, abs_mul, abs_two] at hd
    have hs : |Real.sin ((θ - θ0) / 2)| < c := by
      rw [hc, lt_div_iff₀ hr]; linarith
    have h1 : -(2 * Real.pi) < θ - θ0 := by linarith [hθI.1, hθ0I.2]
    have h2 : θ - θ0 < 2 * Real.pi := by linarith [hθI.2, hθ0I.1]
    rcases sin_half_case (θ - θ0) c h1 h2 hs with h | h
    · left; left
      have := abs_lt.mp h
      exact ⟨by linarith, by linarith⟩
    · rcases le_or_gt 0 (θ - θ0) with h' | h'
      · right
        rw [abs_of_nonneg h'] at h
        exact ⟨by linarith [hθ0I.1], hθI.2⟩
      · left; right
        rw [abs_of_neg h'] at h
        exact ⟨hθI.1, by linarith [hθ0I.2]⟩
  calc volume E ≤ volume (Set.Ioo (θ0 - Real.pi * c) (θ0 + Real.pi * c) ∪ Set.Ioo 0 (Real.pi * c) ∪
      Set.Ioc (2 * Real.pi - Real.pi * c) (2 * Real.pi)) := measure_mono hsub
    _ ≤ volume (Set.Ioo (θ0 - Real.pi * c) (θ0 + Real.pi * c)) + volume (Set.Ioo 0 (Real.pi * c)) +
        volume (Set.Ioc (2 * Real.pi - Real.pi * c) (2 * Real.pi)) :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _) |>.trans_eq
          (by ring)
    _ = ENNReal.ofReal (2 * (Real.pi * c)) + ENNReal.ofReal (Real.pi * c) +
        ENNReal.ofReal (Real.pi * c) := by
        rw [Real.volume_Ioo, Real.volume_Ioo, Real.volume_Ioc]
        congr 2 <;> ring_nf
    _ ≤ ENNReal.ofReal (4 * Real.pi * c) := by
        have hη : 0 < η := lt_of_le_of_lt (norm_nonneg _) hθ0
        have hc0 : 0 < c := div_pos hη hr
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply le_of_eq; congr 1; ring


/-- The Möbius map `w ↦ a + (w + 1)/(w - 1)` from the unit disc onto `Re s < a`. -/
noncomputable def cay (a : ℝ) (w : ℂ) : ℂ := (a : ℂ) + (w + 1) / (w - 1)

lemma re_div_cay (w : ℂ) (hw : w ≠ 1) :
    ((w + 1) / (w - 1)).re = (‖w‖ ^ 2 - 1) / ‖w - 1‖ ^ 2 := by
  have h1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h3 : Complex.normSq (w - 1) = (w.re - 1) ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [Complex.div_re, h1, h2, h3]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im, add_zero, sub_zero]
  rw [← add_div]
  congr 1
  ring

lemma cay_delta (a : ℝ) (w : ℂ) (hw : w ≠ 1) :
    a - (cay a w).re = (1 - ‖w‖ ^ 2) / ‖w - 1‖ ^ 2 := by
  rw [cay, Complex.add_re, Complex.ofReal_re, re_div_cay w hw]
  ring

lemma ne_one_of_norm (w : ℂ) (r : ℝ) (hw : ‖w‖ = r) (hr1 : r < 1) : w ≠ 1 := by
  intro h; rw [h, norm_one] at hw; linarith

lemma delta_pos (a r : ℝ) (hr1 : r < 1) (w : ℂ) (hw : ‖w‖ = r) (hr0 : 0 < r) :
    (1 - r) / 2 ≤ a - (cay a w).re ∧ 0 < a - (cay a w).re := by
  have hw1 := ne_one_of_norm w r hw hr1
  rw [cay_delta a w hw1, hw]
  have hn1 : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
  have hn2 : ‖w - 1‖ ≤ 1 + r := by
    have := norm_sub_le w 1; rw [norm_one, hw] at this; linarith
  have hsq : ‖w - 1‖ ^ 2 ≤ (1 + r) ^ 2 := pow_le_pow_left₀ hn1.le hn2 2
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hsq (by linarith : (0:ℝ) ≤ (1 - r) / 2)
    have h4 : (1 - r) / 2 * (1 + r) ^ 2 ≤ 1 - r ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - r) (by linarith : (0:ℝ) ≤ 1 + r))
        (by linarith : (0:ℝ) ≤ 1 - r)]
    linarith
  · apply div_pos _ (by positivity); nlinarith

lemma kernel_pt (a r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (w u : ℂ) (hw : ‖w‖ = r)
    (h : ‖u - cay a w‖ < (a - (cay a w).re) / 2) :
    (1 - r) / 4 < a - u.re ∧ a - u.re < 3 * (a - (cay a w).re) / 2 ∧
      ‖w - (u - a + 1) / (u - a - 1)‖ < 1 - r := by
  have hw1 := ne_one_of_norm w r hw hr1
  set δ := a - (cay a w).re with hδ_def
  obtain ⟨hδlow, hδpos⟩ := delta_pos a r hr1 w hw hr0
  have hre : |u.re - (cay a w).re| ≤ ‖u - cay a w‖ := by
    have := Complex.abs_re_le_norm (u - cay a w); rwa [Complex.sub_re] at this
  have hre' := abs_lt.mp (lt_of_le_of_lt hre h)
  refine ⟨by linarith [hre'.2], by linarith [hre'.1], ?_⟩
  have hδ : δ = (1 - r ^ 2) / ‖w - 1‖ ^ 2 := by rw [hδ_def, cay_delta a w hw1, hw]
  have hwm1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hn1 : 0 < ‖w - 1‖ := norm_pos_iff.mpr hwm1
  set z := (w + 1) / (w - 1) with hz
  set zu := u - a with hzu
  have hcay : cay a w = a + z := rfl
  have hzzu : ‖z - zu‖ < δ / 2 := by
    have : z - zu = -(u - cay a w) := by rw [hcay, hzu]; ring
    rw [this, norm_neg]; exact h
  have hz1 : z - 1 = 2 / (w - 1) := by rw [hz]; field_simp; ring
  have hz1ne : z - 1 ≠ 0 := by rw [hz1]; exact div_ne_zero two_ne_zero hwm1
  have hnz1 : ‖z - 1‖ = 2 / ‖w - 1‖ := by rw [hz1, norm_div]; simp
  have key3 : δ / (‖z - 1‖ * (‖z - 1‖ / 2)) = (1 - r ^ 2) / 2 := by
    rw [hnz1, hδ]; field_simp
  have hzu1ne : zu - 1 ≠ 0 := by
    intro h0
    have : (zu - 1).re = 0 := by rw [h0]; simp
    rw [hzu, Complex.sub_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re] at this
    linarith [hre'.2]
  have hwz : w = (z + 1) / (z - 1) := by
    rw [eq_div_iff hz1ne, hz1, hz]; field_simp; ring
  have hdiff : w - (zu + 1) / (zu - 1) = 2 * (zu - z) / ((z - 1) * (zu - 1)) := by
    rw [hwz]; field_simp; ring
  have hgoal : w - (u - a + 1) / (u - a - 1) = w - (zu + 1) / (zu - 1) := by rw [hzu]
  rw [hgoal, hdiff, norm_div, norm_mul, norm_mul, Complex.norm_two]
  set A := ‖z - 1‖ with hA
  set B := ‖zu - 1‖ with hB
  have hzre : z.re = -δ := by
    have : (cay a w).re = a + z.re := by rw [hcay]; simp
    rw [hδ_def, this]; ring
  have hA1 : 1 + δ ≤ A := by
    have := Complex.re_le_norm (1 - z)
    rw [Complex.sub_re, Complex.one_re, hzre, norm_sub_rev] at this
    linarith
  have hAB : A ≤ ‖z - zu‖ + B := by
    have : z - 1 = (z - zu) + (zu - 1) := by ring
    rw [hA, this]; exact norm_add_le _ _
  have hApos : 0 < A := by linarith
  have hB2 : A / 2 < B := by linarith
  have hBpos : 0 < B := by linarith
  have hzzu' : ‖zu - z‖ = ‖z - zu‖ := norm_sub_rev _ _
  rw [hzzu']
  have key1 : 2 * ‖z - zu‖ / (A * B) < δ / (A * B) := by
    apply div_lt_div_of_pos_right _ (by positivity); linarith
  have key2 : δ / (A * B) ≤ δ / (A * (A / 2)) := by
    apply div_le_div_of_nonneg_left hδpos.le (by positivity)
    exact mul_le_mul_of_nonneg_left hB2.le hApos.le
  have key4 : (1 - r ^ 2) / 2 ≤ 1 - r := by nlinarith
  linarith


lemma norm_circleMap_r (r θ : ℝ) (hr0 : 0 < r) : ‖circleMap 0 r θ‖ = r := by
  rw [norm_circleMap_zero, abs_of_pos hr0]

lemma continuous_cay_circle (a r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (fun θ : ℝ => cay a (circleMap 0 r θ)) := by
  unfold cay
  refine continuous_const.add (((continuous_circleMap 0 r).add continuous_const).div
    ((continuous_circleMap 0 r).sub continuous_const) (fun θ => ?_))
  exact sub_ne_zero.mpr (ne_one_of_norm _ r (norm_circleMap_r r θ hr0) hr1)

/-- The kernel `1[|u - S(θ)| < δ(θ)/2] · 4/(π δ(θ)²)`. -/
noncomputable def J (a r θ : ℝ) (u : ℂ) : ℝ≥0∞ :=
  if ‖u - cay a (circleMap 0 r θ)‖ < (a - (cay a (circleMap 0 r θ)).re) / 2 then
    ENNReal.ofReal (4 / (Real.pi * (a - (cay a (circleMap 0 r θ)).re) ^ 2)) else 0

/-- The majorant `1[a - σ > (1-r)/4] · 72(1-r)/(a-σ)²`. -/
noncomputable def kk (a r σ : ℝ) : ℝ≥0∞ :=
  if (1 - r) / 4 < a - σ then ENNReal.ofReal (72 * (1 - r) * (a - σ) ^ (-2 : ℝ)) else 0

lemma measurable_J (a r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Measurable (fun p : ℝ × ℂ => J a r p.1 p.2) := by
  have hS := continuous_cay_circle a r hr0 hr1
  have hδ : Continuous (fun θ : ℝ => a - (cay a (circleMap 0 r θ)).re) :=
    continuous_const.sub (Complex.continuous_re.comp hS)
  unfold J
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt (continuous_snd.sub (hS.comp continuous_fst)).norm.measurable
      ((hδ.comp continuous_fst).div_const 2).measurable
  · refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.div (measurable_const.mul ((hδ.comp continuous_fst).measurable.pow_const 2))

lemma arc_bound (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (ζ : ℂ) :
    volume ({θ : ℝ | ‖circleMap 0 r θ - ζ‖ < 1 - r} ∩ Set.Ioc 0 (2 * Real.pi)) ≤
      ENNReal.ofReal (8 * Real.pi * (1 - r)) := by
  have h1 := arc_measure r (1 - r) hr0 ζ
  have h2 : volume ({θ : ℝ | ‖circleMap 0 r θ - ζ‖ < 1 - r} ∩ Set.Ioc 0 (2 * Real.pi)) ≤
      ENNReal.ofReal (2 * Real.pi) := by
    refine (measure_mono Set.inter_subset_right).trans ?_
    rw [Real.volume_Ioc, sub_zero]
  have hpi := Real.pi_pos
  by_cases hr2 : 1 / 2 ≤ r
  · refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have : (1 - r) / r ≤ 2 * (1 - r) := by
      rw [div_le_iff₀ hr0]; nlinarith
    nlinarith
  · refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith

lemma kernel_int (a r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (u : ℂ) :
    ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), J a r θ u ≤ kk a r u.re := by
  by_cases hu : (1 - r) / 4 < a - u.re
  · have hx : 0 < a - u.re := lt_of_le_of_lt (by linarith) hu
    set x := a - u.re with hx_def
    set wu := (u - a + 1) / (u - a - 1) with hwu
    set E := {θ : ℝ | ‖circleMap 0 r θ - wu‖ < 1 - r} with hE
    have hEm : MeasurableSet E :=
      measurableSet_lt ((continuous_circleMap 0 r).sub continuous_const).norm.measurable
        measurable_const
    have hpt : ∀ θ, J a r θ u ≤ E.indicator (fun _ => ENNReal.ofReal (9 / (Real.pi * x ^ 2))) θ := by
      intro θ
      unfold J
      split_ifs with hc
      · obtain ⟨_, h2, h3⟩ := kernel_pt a r hr0 hr1 _ u (norm_circleMap_r r θ hr0) hc
        rw [Set.indicator_of_mem (show θ ∈ E from h3)]
        apply ENNReal.ofReal_le_ofReal
        have hδpos := (delta_pos a r hr1 _ (norm_circleMap_r r θ hr0) hr0).2
        have hpi := Real.pi_pos
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h4 : x ^ 2 ≤ (3 * (a - (cay a (circleMap 0 r θ)).re) / 2) ^ 2 :=
          pow_le_pow_left₀ hx.le h2.le 2
        nlinarith
      · exact bot_le
    calc ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), J a r θ u
        ≤ ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
            E.indicator (fun _ => ENNReal.ofReal (9 / (Real.pi * x ^ 2))) θ := lintegral_mono hpt
      _ = ENNReal.ofReal (9 / (Real.pi * x ^ 2)) * volume (E ∩ Set.Ioc 0 (2 * Real.pi)) := by
          rw [lintegral_indicator_const hEm, Measure.restrict_apply hEm]
      _ ≤ ENNReal.ofReal (9 / (Real.pi * x ^ 2)) * ENNReal.ofReal (8 * Real.pi * (1 - r)) := by
          gcongr; exact arc_bound r hr0 hr1 wu
      _ = kk a r u.re := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          unfold kk
          rw [if_pos hu]
          congr 1
          rw [Real.rpow_neg hx.le, Real.rpow_two]
          field_simp
          ring
  · have h0 : ∀ θ, J a r θ u = 0 := by
      intro θ
      unfold J
      rw [if_neg]
      intro hc
      exact hu (kernel_pt a r hr0 hr1 _ u (norm_circleMap_r r θ hr0) hc).1
    simp only [h0, lintegral_zero]
    exact bot_le

lemma kk_integral (a r : ℝ) (hr1 : r < 1) : ∫⁻ σ, kk a r σ = ENNReal.ofReal 288 := by
  set c := (1 - r) / 4 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set g : ℝ → ℝ≥0∞ := (Set.Ioi c).indicator (fun x => ENNReal.ofReal (72 * (1 - r) * x ^ (-2 : ℝ)))
    with hg
  have hkg : (fun σ => kk a r σ) = fun σ => g (a - σ) := by
    funext σ
    simp only [kk, hg, Set.indicator, Set.mem_Ioi, hc]
  rw [hkg, lintegral_sub_left_eq_self g a, hg, lintegral_indicator measurableSet_Ioi]
  have hint : IntegrableOn (fun x : ℝ => 72 * (1 - r) * x ^ (-2 : ℝ)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hc0).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hc0]
    rw [show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, hc]
    have : (1 - r) ≠ 0 := by linarith
    field_simp
    ring
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have : 0 < x := lt_trans hc0 hx
    have : 0 < 1 - r := by linarith
    positivity


lemma main_bound (Φ : ℂ → ℂ) (a q : ℝ) (hq : 0 < q) (N : ℝ≥0∞)
    (hd : DifferentiableOn ℂ Φ {s : ℂ | s.re < a})
    (hline : ∀ σ : ℝ, σ < a → ∫⁻ t : ℝ, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ₑ ^ q ≤ N)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ‖Φ (cay a (circleMap 0 r θ))‖ₑ ^ q ≤
      ENNReal.ofReal 288 * N := by
  classical
  set H := {s : ℂ | s.re < a} with hH_def
  have hH : IsOpen H := isOpen_lt Complex.continuous_re continuous_const
  set Φ' : ℂ → ℂ := H.piecewise Φ (fun _ => 0) with hΦ'_def
  have hΦ'm : Measurable Φ' :=
    ContinuousOn.measurable_piecewise hd.continuousOn continuousOn_const hH.measurableSet
  have hΦ'eq : ∀ s ∈ H, Φ' s = Φ s := fun s hs => Set.piecewise_eq_of_mem _ _ _ hs
  have hΦ'd : DifferentiableOn ℂ Φ' H := hd.congr (fun s hs => hΦ'eq s hs)
  set v : ℂ → ℝ≥0∞ := fun u => ‖Φ' u‖ₑ ^ q with hv_def
  have hvm : Measurable v := hΦ'm.enorm.pow_const q
  have hJm := measurable_J a r hr0 hr1
  -- Step 1: sub-mean value property on the discs `D(S(θ), δ(θ)/2)`
  have step1 : ∀ θ : ℝ, ‖Φ (cay a (circleMap 0 r θ))‖ₑ ^ q ≤ ∫⁻ u, J a r θ u * v u := by
    intro θ
    set S := cay a (circleMap 0 r θ) with hS
    set δ := a - S.re with hδ
    have hδpos : 0 < δ := (delta_pos a r hr1 _ (norm_circleMap_r r θ hr0) hr0).2
    have hSH : S ∈ H := by show S.re < a; linarith
    have hsub : closedBall S (δ / 2) ⊆ H := by
      intro w hw
      have h1 : |w.re - S.re| ≤ δ / 2 := by
        have := Complex.abs_re_le_norm (w - S)
        rw [Complex.sub_re] at this
        rw [mem_closedBall, dist_eq_norm] at hw
        linarith
      show w.re < a
      have := (abs_le.mp h1).2
      linarith
    have hdm := disc_mean Φ' H hH hΦ'd hΦ'm S (δ / 2) q (by positivity) hq hsub
    have hJ : ∫⁻ u, J a r θ u * v u =
        ENNReal.ofReal (4 / (Real.pi * δ ^ 2)) * ∫⁻ u in ball S (δ / 2), v u := by
      have : (fun u => J a r θ u * v u) =
          (ball S (δ / 2)).indicator (fun u => ENNReal.ofReal (4 / (Real.pi * δ ^ 2)) * v u) := by
        funext u
        simp only [J, Set.indicator, mem_ball, dist_eq_norm]
        split_ifs <;> simp_all
      rw [this, lintegral_indicator measurableSet_ball, lintegral_const_mul _ hvm]
    rw [hJ, ← hΦ'eq S hSH, ← ofReal_norm_rpow _ q hq.le]
    have hpi := Real.pi_pos
    calc ENNReal.ofReal (‖Φ' S‖ ^ q)
        = ENNReal.ofReal (4 / (Real.pi * δ ^ 2)) *
            ENNReal.ofReal (Real.pi * (δ / 2) ^ 2 * ‖Φ' S‖ ^ q) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
          ring
      _ ≤ ENNReal.ofReal (4 / (Real.pi * δ ^ 2)) * ∫⁻ u in ball S (δ / 2), v u := by
          gcongr
  -- Step 2: Tonelli
  have hmeas2 : Measurable (Function.uncurry fun θ u => J a r θ u * v u) :=
    hJm.mul (hvm.comp measurable_snd)
  calc ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ‖Φ (cay a (circleMap 0 r θ))‖ₑ ^ q
      ≤ ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ∫⁻ u, J a r θ u * v u := lintegral_mono step1
    _ = ∫⁻ u, ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), J a r θ u * v u :=
        lintegral_lintegral_swap hmeas2.aemeasurable
    _ = ∫⁻ u, (∫⁻ θ in Set.Ioc 0 (2 * Real.pi), J a r θ u) * v u := by
        congr 1; funext u
        exact lintegral_mul_const _ (hJm.comp (measurable_id.prodMk measurable_const))
    _ ≤ ∫⁻ u, kk a r u.re * v u := by
        gcongr with u
        exact kernel_int a r hr0 hr1 u
    _ ≤ ENNReal.ofReal 288 * N := by
        have hkm : Measurable (fun σ : ℝ => kk a r σ) := by
          unfold kk
          refine Measurable.ite (measurableSet_lt measurable_const
            (measurable_const.sub measurable_id)) ?_ measurable_const
          exact ENNReal.measurable_ofReal.comp
            (measurable_const.mul ((measurable_const.sub measurable_id).pow_const _))
        have hfm : Measurable (fun u : ℂ => kk a r u.re * v u) :=
          (hkm.comp Complex.measurable_re).mul hvm
        have hmp := Complex.volume_preserving_equiv_real_prod.symm
        rw [← hmp.lintegral_comp hfm, Measure.volume_eq_prod,
          lintegral_prod (fun z : ℝ × ℝ => kk a r (Complex.measurableEquivRealProd.symm z).re *
            v (Complex.measurableEquivRealProd.symm z)) (hfm.comp hmp.measurable).aemeasurable]
        have hval : ∀ x y : ℝ, Complex.measurableEquivRealProd.symm (x, y) =
            (x : ℂ) + (y : ℂ) * I := by
          intro x y
          apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
        calc ∫⁻ x : ℝ, ∫⁻ y : ℝ, kk a r (Complex.measurableEquivRealProd.symm (x, y)).re *
              v (Complex.measurableEquivRealProd.symm (x, y))
            = ∫⁻ x : ℝ, kk a r x * ∫⁻ y : ℝ, v ((x : ℂ) + (y : ℂ) * I) := by
              congr 1; funext x
              simp only [hval]
              have hre : ∀ y : ℝ, ((x : ℂ) + (y : ℂ) * I).re = x := by intro y; simp
              simp only [hre]
              exact lintegral_const_mul _ (hvm.comp (by fun_prop))
          _ ≤ ∫⁻ x : ℝ, kk a r x * N := by
              refine lintegral_mono (fun x => ?_)
              unfold kk
              split_ifs with hx
              · gcongr
                have hxa : x < a := by linarith
                calc ∫⁻ y : ℝ, v ((x : ℂ) + (y : ℂ) * I)
                    = ∫⁻ y : ℝ, ‖Φ ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ q := by
                      congr 1; funext y
                      simp only [hv_def]
                      rw [hΦ'eq]
                      show ((x : ℂ) + (y : ℂ) * I).re < a
                      simpa using hxa
                  _ ≤ N := hline x hxa
              · simp
          _ = (∫⁻ x : ℝ, kk a r x) * N := lintegral_mul_const _ hkm
          _ = ENNReal.ofReal 288 * N := by rw [kk_integral a r hr1]


lemma enorm_le_eLpNorm_top (g : ℝ → ℂ) (hg : Continuous g) (y0 : ℝ) :
    ‖g y0‖ₑ ≤ eLpNorm g ⊤ volume := by
  rw [eLpNorm_exponent_top]
  unfold eLpNormEssSup
  by_contra hlt
  rw [not_le] at hlt
  set M := essSup (fun x => ‖g x‖ₑ) volume with hM
  have hU : IsOpen {y | M < ‖g y‖ₑ} := isOpen_lt continuous_const hg.enorm
  have hpos : volume {y | M < ‖g y‖ₑ} ≠ 0 := hU.measure_ne_zero volume ⟨y0, hlt⟩
  have hae := ENNReal.ae_le_essSup (fun x => ‖g x‖ₑ) (μ := volume)
  rw [ae_iff] at hae
  apply hpos
  simpa [not_le] using hae

end Sol_HardyHalfPlane_exists_bound_circle_eLpNorm_comp_cayley

open HardyHalfPlane Sol_HardyHalfPlane_exists_bound_circle_eLpNorm_comp_cayley

theorem solution (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp0 : p ≠ 0)
    (hΦ : MemLeftHardy Φ a p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ r : ℝ, 0 < r → r < 1 →
      eLpNorm (fun θ : ℝ => Φ ((a : ℂ) + (circleMap 0 r θ + 1) / (circleMap 0 r θ - 1))) p
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) ≤ C := by
  set N := leftHardyNorm Φ a p with hN_def
  have hN : N < ⊤ := hΦ.2
  have hd := hΦ.1
  have hlineE : ∀ σ : ℝ, σ < a →
      eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) p volume ≤ N := by
    intro σ hσ
    rw [hN_def]; unfold leftHardyNorm
    exact le_iSup₂ (f := fun σ (_ : σ < a) =>
      eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) p volume) σ hσ
  by_cases hpt : p = ⊤
  · subst hpt
    refine ⟨N, hN, fun r hr0 hr1 => ?_⟩
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    refine Eventually.of_forall (fun θ => ?_)
    show ‖Φ (cay a (circleMap 0 r θ))‖ₑ ≤ N
    set s := cay a (circleMap 0 r θ) with hs_def
    have hs : s.re < a := by
      have := (delta_pos a r hr1 _ (norm_circleMap_r r θ hr0) hr0).2
      linarith
    have hg : Continuous (fun y : ℝ => Φ ((s.re : ℂ) + (y : ℂ) * Complex.I)) := by
      refine hd.continuousOn.comp_continuous (by fun_prop) (fun y => ?_)
      show ((s.re : ℂ) + (y : ℂ) * Complex.I).re < a
      simpa using hs
    have h1 := enorm_le_eLpNorm_top _ hg s.im
    have h2 : ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = s := Complex.re_add_im s
    simp only [h2] at h1
    exact h1.trans (hlineE s.re hs)
  · set q := p.toReal with hq_def
    have hq : 0 < q := ENNReal.toReal_pos hp0 hpt
    have hline : ∀ σ : ℝ, σ < a →
        ∫⁻ t : ℝ, ‖Φ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ₑ ^ q ≤ N ^ q := by
      intro σ hσ
      have h2 := hlineE σ hσ
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt] at h2
      have := ENNReal.rpow_le_rpow h2 hq.le
      rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one] at this
    refine ⟨(ENNReal.ofReal 288 * N ^ q) ^ (1 / q), ?_, fun r hr0 hr1 => ?_⟩
    · apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le hN.ne)
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
      exact ENNReal.rpow_le_rpow (main_bound Φ a q hq (N ^ q) hd hline r hr0 hr1) (by positivity)
