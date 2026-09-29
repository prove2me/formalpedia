-- Prove2me | solution 1 for MeasureTheory.integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/db2f464a-fe9d-59f4-8f02-8fc50e5c8c81

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le

set_option autoImplicit false

noncomputable section

namespace P2mScattLip

open MeasureTheory Set Metric Filter intervalIntegral
open scoped Topology

theorem continuousOn_deriv_param {X : Type*} [TopologicalSpace X] (N : ℂ → X → ℂ) (O : Set ℂ)
    (hO : IsOpen O) (hN : ContinuousOn (fun p : ℂ × X => N p.1 p.2) (O ×ˢ univ))
    (hNa : ∀ x : X, AnalyticOnNhd ℂ (fun s => N s x) O) :
    ContinuousOn (fun p : ℂ × X => deriv (fun s => N s p.2) p.1) (O ×ˢ univ) := by
  rintro ⟨s₀, x₀⟩ ⟨hs₀, -⟩
  obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.mp hO s₀ hs₀
  set r : ℝ := R / 3 with hr_def
  have hr : 0 < r := by positivity
  have h2r : closedBall s₀ (2 * r) ⊆ O :=
    (closedBall_subset_ball (by rw [hr_def]; linarith)).trans hRO
  have hdiff : ∀ x : X, DifferentiableOn ℂ (fun s => N s x) O := fun x =>
    (hNa x).analyticOn.differentiableOn
  have hd : ContinuousAt (deriv fun s => N s x₀) s₀ := ((hNa x₀).deriv s₀ hs₀).continuousAt
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hcont : ContinuousOn (Function.uncurry fun (x : X) (s : ℂ) => N s x)
      (univ ×ˢ closedBall s₀ (2 * r)) := by
    have hsw : Continuous fun p : X × ℂ => ((p.2, p.1) : ℂ × X) := by fun_prop
    refine (hN.comp hsw.continuousOn ?_)
    rintro ⟨x, s⟩ ⟨-, hs⟩
    exact ⟨h2r hs, mem_univ _⟩
  have hεr : 0 < ε / 2 * r := by positivity
  obtain ⟨v, hv, hvN⟩ := IsCompact.mem_uniformity_of_prod (isCompact_closedBall s₀ (2 * r)) hcont
    (mem_univ x₀) (Metric.dist_mem_uniformity hεr)
  rw [nhdsWithin_univ] at hv
  have hd' : ∀ᶠ s in 𝓝 s₀, dist (deriv (fun s => N s x₀) s) (deriv (fun s => N s x₀) s₀) < ε / 2 :=
    Metric.tendsto_nhds.mp hd (ε / 2) (by positivity)
  have hball : ∀ᶠ s in 𝓝 s₀, s ∈ ball s₀ r := ball_mem_nhds s₀ hr
  have hprod : ∀ᶠ p in 𝓝[O ×ˢ univ] ((s₀, x₀) : ℂ × X),
      (p.1 ∈ ball s₀ r ∧ dist (deriv (fun s => N s x₀) p.1) (deriv (fun s => N s x₀) s₀) < ε / 2) ∧
        p.2 ∈ v := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    rw [nhds_prod_eq]
    exact Filter.Eventually.prod_mk (hball.and hd') hv
  filter_upwards [hprod] with p hp
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  set s := p.1
  set x := p.2
  have hsub : closedBall s r ⊆ closedBall s₀ (2 * r) := by
    refine closedBall_subset_closedBall' ?_
    have : dist s s₀ < r := mem_ball.mp hp1
    linarith
  have hsO : closedBall s r ⊆ O := hsub.trans h2r
  have hds : deriv (fun s => N s x) s = Complex.cderiv r (fun s => N s x) s :=
    (Complex.cderiv_eq_deriv hO (hdiff x) hr hsO).symm
  have hds₀ : deriv (fun s => N s x₀) s = Complex.cderiv r (fun s => N s x₀) s :=
    (Complex.cderiv_eq_deriv hO (hdiff x₀) hr hsO).symm
  have hsphere : ∀ w ∈ sphere s r, ‖N w x - N w x₀‖ < ε / 2 * r := by
    intro w hw
    have hw' : w ∈ closedBall s₀ (2 * r) := hsub (sphere_subset_closedBall hw)
    have := hvN x hp3 w hw'
    rwa [Set.mem_setOf_eq, dist_eq_norm] at this
  have hcx : ContinuousOn (fun s => N s x) (sphere s r) :=
    (hdiff x).continuousOn.mono ((sphere_subset_closedBall).trans hsO)
  have hcx₀ : ContinuousOn (fun s => N s x₀) (sphere s r) :=
    (hdiff x₀).continuousOn.mono ((sphere_subset_closedBall).trans hsO)
  have h1 : ‖deriv (fun s => N s x) s - deriv (fun s => N s x₀) s‖ < ε / 2 := by
    rw [hds, hds₀]
    have := Complex.norm_cderiv_sub_lt hr hsphere hcx hcx₀
    rwa [mul_div_assoc, div_self hr.ne', mul_one] at this
  have h2 : ‖deriv (fun s => N s x₀) s - deriv (fun s => N s x₀) s₀‖ < ε / 2 := by
    rw [← dist_eq_norm]; exact hp2
  show dist (deriv (fun s => N s x) s) (deriv (fun s => N s x₀) s₀) < ε
  rw [dist_eq_norm]
  calc ‖deriv (fun s => N s x) s - deriv (fun s => N s x₀) s₀‖
      = ‖(deriv (fun s => N s x) s - deriv (fun s => N s x₀) s) +
          (deriv (fun s => N s x₀) s - deriv (fun s => N s x₀) s₀)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖deriv (fun s => N s x) s - deriv (fun s => N s x₀) s‖ +
          ‖deriv (fun s => N s x₀) s - deriv (fun s => N s x₀) s₀‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

theorem sq_integral_norm_le {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ τ in Ioc a b, ‖g τ‖) ^ 2 ≤ (b - a) * ∫ τ in Ioc a b, ‖g τ‖ ^ 2 := by
  set μI : Measure ℝ := volume.restrict (Ioc a b) with hμI
  haveI : IsFiniteMeasure μI :=
    ⟨by rw [hμI, Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hg.continuousOn
  have hgm : MemLp g (ENNReal.ofReal 2) μI :=
    MemLp.of_bound hg.aestronglyMeasurable C
      (ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ => hC τ (Ioc_subset_Icc_self hτ))
  have h1m : MemLp (fun _ : ℝ => (1 : ℂ)) (ENNReal.ofReal 2) μI := memLp_const 1
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hgm h1m
  have hI1 : (∫ _ : ℝ, ‖(1 : ℂ)‖ ^ (2 : ℝ) ∂μI) = b - a := by
    simp only [norm_one, Real.one_rpow]
    rw [hμI, setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul, mul_one]
  have hL : (∫ τ, ‖g τ‖ * ‖(1 : ℂ)‖ ∂μI) = ∫ τ, ‖g τ‖ ∂μI := by
    simp only [norm_one, mul_one]
  have hP : (∫ τ, ‖g τ‖ ^ (2 : ℝ) ∂μI) = ∫ τ, ‖g τ‖ ^ 2 ∂μI := by
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [Real.rpow_two]
  rw [hI1, hL, hP] at h
  have hA : 0 ≤ ∫ τ, ‖g τ‖ ∂μI := integral_nonneg fun _ => norm_nonneg _
  have hPn : 0 ≤ ∫ τ, ‖g τ‖ ^ 2 ∂μI := integral_nonneg fun _ => by positivity
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  calc (∫ τ, ‖g τ‖ ∂μI) ^ 2
      ≤ ((∫ τ, ‖g τ‖ ^ 2 ∂μI) ^ (1 / (2 : ℝ)) * (b - a) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hA h 2
    _ = (b - a) * ∫ τ, ‖g τ‖ ^ 2 ∂μI := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hPn, Real.sq_sqrt hba, mul_comm]

theorem main {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (O : Set ℂ) (hO : IsOpen O) (hO₀ : {s : ℂ | s.re = 0} ⊆ O)
    (N : ℂ → X → ℂ) (hNa : ∀ x : X, AnalyticOnNhd ℂ (fun s => N s x) O)
    (hNc : ContinuousOn (fun p : ℂ × X => N p.1 p.2) (O ×ˢ Set.univ))
    (t t' B : ℝ)
    (hB : ∀ τ ∈ Set.uIcc t t',
      ∫ x, ‖deriv (fun s : ℂ => N s x) ((τ : ℂ) * Complex.I)‖ ^ 2 ∂μ ≤ B ^ 2) :
    ∫ x, ‖N ((t : ℂ) * Complex.I) x - N ((t' : ℂ) * Complex.I) x‖ ^ 2 ∂μ ≤ (B * |t - t'|) ^ 2 := by
  wlog htt : t ≤ t' generalizing t t'
  · have h := this t' t (by rwa [Set.uIcc_comm]) (le_of_not_ge htt)
    simpa only [norm_sub_rev, abs_sub_comm] using h

  set D : ℝ → X → ℂ := fun τ x => deriv (fun s : ℂ => N s x) ((τ : ℂ) * Complex.I) with hD
  have hax : ∀ τ : ℝ, ((τ : ℂ) * Complex.I) ∈ O := fun τ => hO₀ (by simp)
  have hDc : Continuous (fun p : X × ℝ => D p.2 p.1) := by
    have h1 := continuousOn_deriv_param N O hO hNc hNa
    have h2 : Continuous (fun p : X × ℝ => ((((p.2 : ℝ) : ℂ) * Complex.I), p.1) : X × ℝ → ℂ × X) := by
      fun_prop
    exact h1.comp_continuous h2 (fun p => ⟨hax _, mem_univ _⟩)
  have hDcx : ∀ x : X, Continuous fun τ : ℝ => D τ x := fun x =>
    hDc.comp (continuous_const.prodMk continuous_id)

  have hderiv : ∀ (x : X) (τ : ℝ),
      HasDerivAt (fun y : ℝ => N ((y : ℂ) * Complex.I) x) (D τ x * Complex.I) τ := by
    intro x τ
    have h1 : HasDerivAt (fun s : ℂ => N s x) (D τ x) ((τ : ℂ) * Complex.I) :=
      ((hNa x _ (hax τ)).differentiableAt).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => z * Complex.I) Complex.I (τ : ℂ) := hasDerivAt_mul_const _
    have h3 := HasDerivAt.comp (τ : ℂ) h1 h2
    exact h3.comp_ofReal

  have hpt : ∀ x : X,
      ‖N ((t : ℂ) * Complex.I) x - N ((t' : ℂ) * Complex.I) x‖ ^ 2 ≤
        (t' - t) * ∫ τ in Ioc t t', ‖D τ x‖ ^ 2 := by
    intro x
    have hftc : ∫ τ in t..t', D τ x * Complex.I =
        N ((t' : ℂ) * Complex.I) x - N ((t : ℂ) * Complex.I) x :=
      integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv x τ)
        (((hDcx x).mul continuous_const).intervalIntegrable t t')
    have hn : ‖N ((t : ℂ) * Complex.I) x - N ((t' : ℂ) * Complex.I) x‖ ≤ ∫ τ in Ioc t t', ‖D τ x‖ := by
      rw [norm_sub_rev, ← hftc]
      refine (intervalIntegral.norm_integral_le_integral_norm htt).trans_eq ?_
      rw [integral_of_le htt]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [norm_mul, Complex.norm_I, mul_one]
    calc ‖N ((t : ℂ) * Complex.I) x - N ((t' : ℂ) * Complex.I) x‖ ^ 2
        ≤ (∫ τ in Ioc t t', ‖D τ x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ (t' - t) * ∫ τ in Ioc t t', ‖D τ x‖ ^ 2 := sq_integral_norm_le htt _ (hDcx x)

  set μI : Measure ℝ := volume.restrict (Ioc t t') with hμI
  haveI : IsFiniteMeasure μI :=
    ⟨by rw [hμI, Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hφc : Continuous (fun p : X × ℝ => ‖D p.2 p.1‖ ^ 2) := (hDc.norm).pow 2
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc t t'))).exists_bound_of_continuousOn
    hφc.continuousOn
  have hInt : Integrable (Function.uncurry fun (x : X) (τ : ℝ) => ‖D τ x‖ ^ 2) (μ.prod μI) := by
    refine Integrable.of_bound hφc.aestronglyMeasurable C ?_
    have hμ : μ.prod μI = (μ.prod volume).restrict (univ ×ˢ Ioc t t') := by
      calc μ.prod μI = (μ.restrict univ).prod (volume.restrict (Ioc t t')) := by rw [Measure.restrict_univ]
        _ = (μ.prod volume).restrict (univ ×ˢ Ioc t t') := Measure.prod_restrict _ _
    rw [hμ, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioc)]
    exact ae_of_all _ fun p hp => hC p ⟨mem_univ _, Ioc_subset_Icc_self hp.2⟩

  have hG : Integrable (fun x : X => ∫ τ, ‖D τ x‖ ^ 2 ∂μI) μ := hInt.integral_prod_left
  have hswap : ∫ x, ∫ τ, ‖D τ x‖ ^ 2 ∂μI ∂μ = ∫ τ, ∫ x, ‖D τ x‖ ^ 2 ∂μ ∂μI :=
    integral_integral_swap hInt
  have hslice : ∫ τ, ∫ x, ‖D τ x‖ ^ 2 ∂μ ∂μI ≤ ∫ _ : ℝ, B ^ 2 ∂μI := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun τ => integral_nonneg fun x => by positivity)
      (integrable_const _) ?_
    rw [hμI]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ => hB τ ?_
    rw [Set.uIcc_of_le htt]
    exact Ioc_subset_Icc_self hτ
  have hconst : ∫ _ : ℝ, B ^ 2 ∂μI = (t' - t) * B ^ 2 := by
    rw [hμI, setIntegral_const, Real.volume_real_Ioc_of_le htt, smul_eq_mul]
  have habs : |t - t'| = t' - t := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 htt)]
  calc ∫ x, ‖N ((t : ℂ) * Complex.I) x - N ((t' : ℂ) * Complex.I) x‖ ^ 2 ∂μ
      ≤ ∫ x, (t' - t) * ∫ τ, ‖D τ x‖ ^ 2 ∂μI ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) (hG.const_mul _)
          (Eventually.of_forall fun x => hpt x)
    _ = (t' - t) * ∫ τ, ∫ x, ‖D τ x‖ ^ 2 ∂μ ∂μI := by rw [MeasureTheory.integral_const_mul, hswap]
    _ ≤ (t' - t) * ((t' - t) * B ^ 2) := by
        rw [← hconst]
        exact mul_le_mul_of_nonneg_left hslice (sub_nonneg.2 htt)
    _ = (B * |t - t'|) ^ 2 := by rw [habs]; ring

end P2mScattLip

end

open MeasureTheory in
theorem solution
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (O : Set ℂ) (hO : IsOpen O) (hO₀ : {s : ℂ | s.re = 0} ⊆ O)
    (N : ℂ → X → ℂ) (hNa : ∀ x : X, AnalyticOnNhd ℂ (fun s => N s x) O)
    (hNc : ContinuousOn (fun p : ℂ × X => N p.1 p.2) (O ×ˢ Set.univ))
    (t t' B : ℝ)
    (hB : ∀ τ ∈ Set.uIcc t t',
      ∫ x, ‖deriv (fun s : ℂ => N s x) ((τ : ℂ) * Complex.I)‖ ^ 2 ∂μ ≤ B ^ 2) :
    ∫ x, ‖N ((t : ℂ) * Complex.I) x - N ((t' : ℂ) * Complex.I) x‖ ^ 2 ∂μ ≤ (B * |t - t'|) ^ 2 :=
  P2mScattLip.main μ O hO hO₀ N hNa hNc t t' B hB

end S_MeasureTheory_integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le
end P2MW
export P2MW.S_MeasureTheory_integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le (solution)
