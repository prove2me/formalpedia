-- Prove2me | solution 1 for LeblSCV.Levi.tomato_can
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T16:54:04.538204+00:00
-- url     : https://prove2.me/submissions/331b4c16-378b-40d6-92ea-440745f90133

import Mathlib
import Definitions.Def_LeblSCV_Shared_IsDomainOfHolomorphy
import Definitions.Def_LeblSCV_Levi_HasSmoothBoundary
import Definitions.Def_LeblSCV_Levi_holTangent
import Definitions.Def_LeblSCV_Levi_leviForm
import Definitions.Def_LeblSCV_Levi_wirtingerZ
import Definitions.Def_LeblSCV_Levi_complexHessian

/-! Blocker 75db3287 `LeblSCV.Levi.hartogs_figure_extension`, built inside the fe5a3ef1 relay.
Chunk A: several-variable identity theorem on any complex normed space.
Chunk B: a complex differentiable function on an open set of a finite-dimensional space is C^1
(its derivative is continuous), via the Cauchy formula for the derivative along complex lines. -/

set_option autoImplicit false

open Filter Topology Set Complex MeasureTheory Real Interval

namespace HFE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Vanishing propagates along complex lines inside a ball. -/
theorem eqOn_zero_ball {f : E → ℂ} {z a : E} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball z r)) (ha : a ∈ Metric.ball z r)
    (h0 : f =ᶠ[𝓝 a] 0) : EqOn f 0 (Metric.ball z r) := by
  intro w hw
  set φ : ℂ → E := fun t => a + t • (w - a) with hφ
  have hφd : Differentiable ℂ φ := by
    intro t
    simp only [hφ]
    fun_prop
  have hφc : Continuous φ := hφd.continuous
  set T : Set ℂ := φ ⁻¹' Metric.ball z r with hT
  have hTo : IsOpen T := Metric.isOpen_ball.preimage hφc
  let φA : ℂ →ᵃ[ℝ] E :=
    ⟨φ, (LinearMap.toSpanSingleton ℂ E (w - a)).restrictScalars ℝ, fun p v => by
      simp only [hφ, vadd_eq_add, LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply,
        add_smul]
      abel⟩
  have hTc : Convex ℝ T := (convex_ball z r).affine_preimage φA
  have hg : DifferentiableOn ℂ (f ∘ φ) T := hf.comp hφd.differentiableOn (fun t ht => ht)
  have hga : AnalyticOnNhd ℂ (f ∘ φ) T := hg.analyticOnNhd hTo
  have h0T : (0 : ℂ) ∈ T := by simp [hT, hφ, ha]
  have h1T : (1 : ℂ) ∈ T := by simp [hT, hφ, hw]
  have hev : (f ∘ φ) =ᶠ[𝓝 0] 0 := by
    have htend : Tendsto φ (𝓝 0) (𝓝 a) := by
      have := hφc.tendsto 0
      simpa [hφ] using this
    filter_upwards [htend.eventually h0] with t ht
    simpa using ht
  have := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero hTc.isPreconnected h0T hev h1T
  simpa [hφ] using this

/-- Identity theorem for complex differentiable functions of several variables. -/
theorem eqOn_zero_of_preconnected {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : E → ℂ} (hf : DifferentiableOn ℂ f U) {z₀ : E} (hz₀ : z₀ ∈ U)
    (h0 : f =ᶠ[𝓝 z₀] 0) : EqOn f 0 U := by
  have hAo : IsOpen {z | f =ᶠ[𝓝 z] 0} := isOpen_setOfPred_eventually_nhds
  have hsub : U ⊆ {z | f =ᶠ[𝓝 z] 0} := by
    refine hUc.subset_of_closure_inter_subset hAo ⟨z₀, hz₀, h0⟩ ?_
    rintro z ⟨hzc, hzU⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hzU
    obtain ⟨a, haA, hda⟩ := Metric.mem_closure_iff.1 hzc r hr
    have hab : a ∈ Metric.ball z r := Metric.mem_ball.2 (by rwa [dist_comm])
    exact Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds z hr)
      (eqOn_zero_ball (hf.mono hrU) hab haA)
  intro z hz
  exact (hsub hz).eq_of_nhds

/-- Two holomorphic functions agreeing near a point of a domain agree on it. -/
theorem eqOn_of_preconnected {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f g : E → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {z₀ : E} (hz₀ : z₀ ∈ U) (h0 : f =ᶠ[𝓝 z₀] g) : EqOn f g U := by
  have h := eqOn_zero_of_preconnected hU hUc (hf.sub hg) hz₀
    (by filter_upwards [h0] with x hx; simp [hx])
  intro z hz
  exact sub_eq_zero.1 (h hz)

/-- Two holomorphic functions agreeing on a nonempty open subset of a domain agree on it. -/
theorem eqOn_of_preconnected_of_open {U V : Set E} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f g : E → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hVne : V.Nonempty) (hfg : EqOn f g V) : EqOn f g U := by
  obtain ⟨z₀, hz₀⟩ := hVne
  exact eqOn_of_preconnected hU hUc hf hg (hVU hz₀)
    (Filter.eventuallyEq_of_mem (hV.mem_nhds hz₀) hfg)

/-- Derivative along a direction as a Cauchy integral over a circle in the line parameter. -/
theorem fderiv_apply_eq_circleIntegral {f : E → ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) {x v : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : ∀ t : ℂ, ‖t‖ ≤ ρ → x + t • v ∈ Ω) :
    fderiv ℂ f x v =
      (2 * π * I : ℂ)⁻¹ • ∮ t in C(0, ρ), ((t - 0) ^ 2)⁻¹ • f (x + t • v) := by
  set L : ℂ → E := fun t => x + t • v with hL
  have hLc : Continuous L := by simp only [hL]; fun_prop
  set U : Set ℂ := L ⁻¹' Ω with hU
  have hUo : IsOpen U := hΩ.preimage hLc
  have hcb : Metric.closedBall (0 : ℂ) ρ ⊆ U := by
    intro t ht
    exact hsub t (by simpa using ht)
  have hgd : DifferentiableOn ℂ (fun t => f (L t)) U := by
    refine hf.comp ?_ (fun t ht => ht)
    intro t _
    simp only [hL]
    fun_prop
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  rw [two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hUo hcb hgd h0]
  have hx : x ∈ Ω := by simpa using hsub 0 (by simp [hρ.le])
  have hLd : HasDerivAt L v 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    simpa [hL] using this
  have hfd : HasFDerivAt f (fderiv ℂ f x) (L 0) := by
    have : L 0 = x := by simp [hL]
    rw [this]
    exact (hf.differentiableAt (hΩ.mem_nhds hx)).hasFDerivAt
  exact ((hfd.comp_hasDerivAt (0 : ℂ) hLd).deriv).symm

/-- Holomorphic functions on open subsets of finite-dimensional spaces are C^1. -/
theorem continuousOn_fderiv [FiniteDimensional ℂ E] {f : E → ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) : ContinuousOn (fderiv ℂ f) Ω := by
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  rw [continuousOn_clm_apply]
  intro v x₀ hx₀
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  set ρ : ℝ := δ / (4 * (‖v‖ + 1)) with hρdef
  have hv1 : 0 < ‖v‖ + 1 := by positivity
  have hρ : 0 < ρ := by positivity
  have hρv : ρ * ‖v‖ ≤ δ / 4 := by
    rw [hρdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg v]
  -- points `x + t • v` with `x` near `x₀`, `‖t‖ ≤ ρ` stay in `closedBall x₀ (3δ/4)`
  have hnear : ∀ x ∈ Metric.ball x₀ (δ / 2), ∀ t : ℂ, ‖t‖ ≤ ρ →
      x + t • v ∈ Metric.closedBall x₀ (3 * δ / 4) := by
    intro x hx t ht
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : ‖x - x₀‖ < δ / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    have h2 : ‖t • v‖ ≤ δ / 4 := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right ht (norm_nonneg v)).trans hρv
    calc ‖x + t • v - x₀‖ = ‖(x - x₀) + t • v‖ := by congr 1; abel
      _ ≤ ‖x - x₀‖ + ‖t • v‖ := norm_add_le _ _
      _ ≤ 3 * δ / 4 := by linarith
  have hKΩ : Metric.closedBall x₀ (3 * δ / 4) ⊆ Ω := by
    intro y hy
    apply hball
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hy
    linarith
  -- the Cauchy-integral representative
  set G : E → ℂ := fun x =>
    (2 * π * I : ℂ)⁻¹ • ∮ t in C(0, ρ), ((t - 0) ^ 2)⁻¹ • f (x + t • v) with hG
  have hEq : ∀ x ∈ Metric.ball x₀ (δ / 2), fderiv ℂ f x v = G x := by
    intro x hx
    exact fderiv_apply_eq_circleIntegral hΩ hf hρ (fun t ht => hKΩ (hnear x hx t ht))
  suffices hc : ContinuousAt G x₀ by
    have hev : G =ᶠ[𝓝 x₀] fun x => fderiv ℂ f x v :=
      Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds x₀ (by linarith))
        (fun x hx => (hEq x hx).symm)
    exact (hc.congr hev).continuousWithinAt
  rw [hG]
  refine ContinuousAt.smul (f := fun _ : E => (2 * π * I : ℂ)⁻¹)
    (g := fun x => ∮ t in C(0, ρ), ((t - 0) ^ 2)⁻¹ • f (x + t • v)) continuousAt_const ?_
  -- unfold the circle integral and use dominated continuity
  simp only [circleIntegral]
  set F : E → ℝ → ℂ := fun x θ =>
    deriv (circleMap 0 ρ) θ • (((circleMap 0 ρ θ - 0) ^ 2)⁻¹ • f (x + circleMap 0 ρ θ • v))
    with hF
  have hcm : ∀ θ : ℝ, ‖circleMap 0 ρ θ‖ ≤ ρ := by
    intro θ
    simp [abs_of_pos hρ]
  have hne : ∀ θ : ℝ, circleMap 0 ρ θ - 0 ≠ 0 := by
    intro θ
    simpa using circleMap_ne_center (c := (0 : ℂ)) hρ.ne' (θ := θ)
  -- joint continuity on the compact set `closedBall x₀ (δ/2) ×ˢ Icc 0 (2π)`
  have hFc : ContinuousOn (Function.uncurry F)
      (Metric.closedBall x₀ (δ / 4) ×ˢ Set.Icc 0 (2 * π)) := by
    have hfin : ContinuousOn (fun p : E × ℝ => f (p.1 + circleMap 0 ρ p.2 • v))
        (Metric.closedBall x₀ (δ / 4) ×ˢ Set.Icc 0 (2 * π)) := by
      refine hf.continuousOn.comp (by fun_prop) ?_
      rintro ⟨x, θ⟩ ⟨hx, -⟩
      apply hKΩ
      apply hnear x _ _ (hcm θ)
      rw [Metric.mem_closedBall] at hx
      rw [Metric.mem_ball]
      linarith
    have hinv : Continuous (fun θ : ℝ => ((circleMap 0 ρ θ - 0) ^ 2)⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) (fun θ => pow_ne_zero 2 (hne θ))
    have hder : Continuous (fun θ : ℝ => deriv (circleMap 0 ρ) θ) := by
      simp only [deriv_circleMap]
      fun_prop
    exact ((hder.comp continuous_snd).continuousOn).smul
      (((hinv.comp continuous_snd).continuousOn).smul hfin)
  obtain ⟨B, hB⟩ := (((isCompact_closedBall x₀ (δ / 4)).prod isCompact_Icc)).exists_bound_of_continuousOn hFc
  have hδ4 : Metric.ball x₀ (δ / 4) ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ (by linarith)
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => B) ?_ ?_ ?_ ?_
  · filter_upwards [hδ4] with x hx
    have hcx : ContinuousOn (F x) (Set.Icc 0 (2 * π)) := by
      have := hFc.comp (Continuous.continuousOn (by fun_prop : Continuous fun θ : ℝ => (x, θ)))
        (fun θ hθ => ⟨Metric.ball_subset_closedBall hx, hθ⟩)
      exact this
    have hsub : Ι (0 : ℝ) (2 * π) ⊆ Set.Icc 0 (2 * π) := by
      rw [Set.uIoc_of_le (by positivity)]
      exact Set.Ioc_subset_Icc_self
    exact (hcx.mono hsub).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hδ4] with x hx
    refine Filter.Eventually.of_forall (fun θ hθ => ?_)
    have hθ' : θ ∈ Set.Icc 0 (2 * π) := by
      rw [Set.uIoc_of_le (by positivity)] at hθ
      exact Set.Ioc_subset_Icc_self hθ
    exact hB (x, θ) ⟨Metric.ball_subset_closedBall hx, hθ'⟩
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall (fun θ _ => ?_)
    have hmem : x₀ + circleMap 0 ρ θ • v ∈ Ω :=
      hKΩ (hnear x₀ (Metric.mem_ball_self (by linarith)) (circleMap 0 ρ θ) (hcm θ))
    have hfa : ContinuousAt f (x₀ + circleMap 0 ρ θ • v) :=
      (hf.differentiableAt (hΩ.mem_nhds hmem)).continuousAt
    have : ContinuousAt (fun x => f (x + circleMap 0 ρ θ • v)) x₀ :=
      ContinuousAt.comp (f := fun x : E => x + circleMap 0 ρ θ • v) hfa (by fun_prop)
    exact ContinuousAt.smul (f := fun _ : E => deriv (circleMap 0 ρ) θ) continuousAt_const
      (ContinuousAt.smul (f := fun _ : E => ((circleMap 0 ρ θ - 0) ^ 2)⁻¹) continuousAt_const this)

/-! Chunk C: the parametric Cauchy integral is jointly holomorphic. -/

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- Cauchy integral in the first variable, the second variable a parameter. -/
noncomputable def cauchyInt (R : ℝ) (f : ℂ × Y → ℂ) (x : ℂ × Y) : ℂ :=
  ∮ ζ in C(0, R), (ζ - x.1)⁻¹ • f (ζ, x.2)

theorem differentiableOn_cauchyInt [FiniteDimensional ℂ Y] {f : ℂ × Y → ℂ} {Ω : Set (ℂ × Y)}
    (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) {R : ℝ} (hR : 0 < R) {D : Set Y}
    (hD : IsOpen D) (hDΩ : ∀ y ∈ D, ∀ ζ ∈ Metric.sphere (0 : ℂ) R, (ζ, y) ∈ Ω) :
    DifferentiableOn ℂ (cauchyInt R f) (Metric.ball 0 R ×ˢ D) := by
  intro x₀ hx₀
  refine DifferentiableAt.differentiableWithinAt ?_
  set Φ : (ℂ × Y) × ℂ → ℂ := fun p => (p.2 - p.1.1)⁻¹ • f (p.2, p.1.2) with hΦ
  set ΩΦ : Set ((ℂ × Y) × ℂ) := {p | p.2 - p.1.1 ≠ 0} ∩ (fun p => (p.2, p.1.2)) ⁻¹' Ω
    with hΩΦ
  have hΩΦo : IsOpen ΩΦ :=
    (isOpen_ne_fun (by fun_prop) continuous_const).inter (hΩ.preimage (by fun_prop))
  have hΦd : DifferentiableOn ℂ Φ ΩΦ := by
    intro p hp
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun p : (ℂ × Y) × ℂ => (p.2 - p.1.1)⁻¹) p :=
      DifferentiableAt.inv (by fun_prop) hp.1
    have h2 : DifferentiableAt ℂ (fun p : (ℂ × Y) × ℂ => f (p.2, p.1.2)) p := by
      have hfp : DifferentiableAt ℂ f (p.2, p.1.2) := hf.differentiableAt (hΩ.mem_nhds hp.2)
      exact hfp.comp p (by fun_prop)
    exact h1.smul h2
  have hΦ'c : ContinuousOn (fderiv ℂ Φ) ΩΦ := continuousOn_fderiv hΩΦo hΦd
  have hopen : IsOpen (Metric.ball (0 : ℂ) R ×ˢ D) := Metric.isOpen_ball.prod hD
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hopen x₀ hx₀
  have hcb : Metric.closedBall x₀ (ε / 2) ⊆ Metric.ball 0 R ×ˢ D :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεsub
  have hmem : ∀ x ∈ Metric.ball (0 : ℂ) R ×ˢ D, ∀ θ : ℝ, (x, circleMap 0 R θ) ∈ ΩΦ := by
    rintro x ⟨hx1, hx2⟩ θ
    refine ⟨?_, ?_⟩
    · show circleMap 0 R θ - x.1 ≠ 0
      intro h
      have hn : ‖circleMap 0 R θ‖ = R := by simp [abs_of_pos hR]
      rw [sub_eq_zero] at h
      rw [Metric.mem_ball, dist_zero_right] at hx1
      rw [h] at hn
      linarith
    · exact hDΩ x.2 hx2 (circleMap 0 R θ) (circleMap_mem_sphere _ hR.le _)
  set F : ℂ × Y → ℝ → ℂ := fun x θ => deriv (circleMap 0 R) θ • Φ (x, circleMap 0 R θ)
    with hF
  set F' : ℂ × Y → ℝ → (ℂ × Y) →L[ℂ] ℂ := fun x θ =>
    deriv (circleMap 0 R) θ •
      (fderiv ℂ Φ (x, circleMap 0 R θ)).comp (ContinuousLinearMap.inl ℂ (ℂ × Y) ℂ) with hF'
  have hcI : cauchyInt R f = fun x => ∫ θ in (0 : ℝ)..2 * π, F x θ := by
    funext x
    rfl
  rw [hcI]
  have hderc : Continuous (fun θ => deriv (circleMap (0 : ℂ) R) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  have hFc : ContinuousOn (Function.uncurry F) ((Metric.ball 0 R ×ˢ D) ×ˢ univ) := by
    refine (hderc.comp continuous_snd).continuousOn.smul ?_
    refine hΦd.continuousOn.comp (by fun_prop) ?_
    rintro ⟨x, θ⟩ ⟨hx, -⟩
    exact hmem x hx θ
  have hF'c : ContinuousOn (Function.uncurry F') ((Metric.ball 0 R ×ˢ D) ×ˢ univ) := by
    refine (hderc.comp continuous_snd).continuousOn.smul ?_
    have : ContinuousOn (fun p : (ℂ × Y) × ℝ => fderiv ℂ Φ (p.1, circleMap 0 R p.2))
        ((Metric.ball 0 R ×ˢ D) ×ˢ univ) :=
      hΦ'c.comp (by fun_prop) (by rintro ⟨x, θ⟩ ⟨hx, -⟩; exact hmem x hx θ)
    exact this.clm_comp continuousOn_const
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ (ε / 2)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π))).exists_bound_of_continuousOn
    (hF'c.mono (prod_mono hcb (subset_univ _)))
  have hIoc : Ι (0 : ℝ) (2 * π) ⊆ Icc 0 (2 * π) := by
    rw [uIoc_of_le (by positivity)]
    exact Ioc_subset_Icc_self
  have hs : Metric.ball x₀ (ε / 2) ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ (by linarith)
  have hsub' : Metric.ball x₀ (ε / 2) ⊆ Metric.ball 0 R ×ˢ D :=
    Metric.ball_subset_closedBall.trans hcb
  have hcontx : ∀ x ∈ Metric.ball (0 : ℂ) R ×ˢ D, Continuous (F x) := fun x hx =>
    continuousOn_univ.1 (hFc.comp (by fun_prop : Continuous fun θ : ℝ => (x, θ)).continuousOn
      (fun θ _ => ⟨hx, mem_univ _⟩))
  have hcontF' : Continuous (F' x₀) :=
    continuousOn_univ.1 (hF'c.comp (by fun_prop : Continuous fun θ : ℝ => (x₀, θ)).continuousOn
      (fun θ _ => ⟨hx₀, mem_univ _⟩))
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (a := 0) (b := 2 * π) (bound := fun _ => B) (F := F) (F' := F') hs ?_
    ((hcontx x₀ hx₀).intervalIntegrable _ _) hcontF'.aestronglyMeasurable ?_
    intervalIntegrable_const ?_
  · exact key.differentiableAt
  · filter_upwards [hs] with x hx
    exact (hcontx x (hsub' hx)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun θ hθ x hx => ?_)
    exact hB (x, θ) ⟨Metric.ball_subset_closedBall hx, hIoc hθ⟩
  · refine Filter.Eventually.of_forall (fun θ _ x hx => ?_)
    have hxm := hmem x (hsub' hx) θ
    have hΦx : HasFDerivAt Φ (fderiv ℂ Φ (x, circleMap 0 R θ)) (x, circleMap 0 R θ) :=
      (hΦd.differentiableAt (hΩΦo.mem_nhds hxm)).hasFDerivAt
    exact (hΦx.comp x (hasFDerivAt_prodMk_left (𝕜 := ℂ) x (circleMap 0 R θ))).const_smul
      (deriv (circleMap 0 R) θ)

/-! Chunk D/E: Cauchy formula on full slices, and independence of the radius. -/

theorem cauchyInt_eq {f : ℂ × Y → ℂ} {Ω : Set (ℂ × Y)} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) {R : ℝ} {y : Y}
    (hy : ∀ ζ ∈ Metric.closedBall (0 : ℂ) R, (ζ, y) ∈ Ω) {ξ : ℂ}
    (hξ : ξ ∈ Metric.ball (0 : ℂ) R) :
    (2 * π * I : ℂ)⁻¹ • cauchyInt R f (ξ, y) = f (ξ, y) := by
  have hc : ContinuousOn (fun ζ => f (ζ, y)) (Metric.closedBall 0 R) :=
    hf.continuousOn.comp (by fun_prop) (fun ζ hζ => hy ζ hζ)
  have hd : ∀ ζ ∈ Metric.ball (0 : ℂ) R \ (∅ : Set ℂ), DifferentiableAt ℂ (fun ζ => f (ζ, y)) ζ := by
    intro ζ hζ
    have hm : (ζ, y) ∈ Ω := hy ζ (Metric.ball_subset_closedBall hζ.1)
    exact (hf.differentiableAt (hΩ.mem_nhds hm)).comp ζ (by fun_prop)
  exact two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty hξ hc hd

theorem cauchyInt_eq_of_le {f : ℂ × Y → ℂ} {Ω : Set (ℂ × Y)} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {y : Y}
    (hann : ∀ ζ : ℂ, r ≤ ‖ζ‖ → ‖ζ‖ ≤ R → (ζ, y) ∈ Ω) {ξ : ℂ} (hξ : ‖ξ‖ < r) :
    cauchyInt R f (ξ, y) = cauchyInt r f (ξ, y) := by
  have hne : ∀ ζ : ℂ, r ≤ ‖ζ‖ → ζ - ξ ≠ 0 := by
    intro ζ hζ h
    rw [sub_eq_zero] at h
    rw [h] at hζ
    linarith
  have hmemA : ∀ ζ ∈ Metric.closedBall (0 : ℂ) R \ Metric.ball 0 r, r ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ R := by
    rintro ζ ⟨h1, h2⟩
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    rw [Metric.mem_ball, dist_zero_right, not_lt] at h2
    exact ⟨h2, h1⟩
  have hdiff : ∀ ζ : ℂ, r ≤ ‖ζ‖ → ‖ζ‖ ≤ R →
      DifferentiableAt ℂ (fun ζ => (ζ - ξ)⁻¹ • f (ζ, y)) ζ := by
    intro ζ h1 h2
    have hm := hann ζ h1 h2
    have h3 : DifferentiableAt ℂ (fun ζ : ℂ => (ζ - ξ)⁻¹) ζ :=
      DifferentiableAt.inv (by fun_prop) (hne ζ h1)
    exact h3.smul ((hf.differentiableAt (hΩ.mem_nhds hm)).comp ζ (by fun_prop))
  unfold cauchyInt
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    Set.countable_empty ?_ ?_
  · intro ζ hζ
    obtain ⟨h1, h2⟩ := hmemA ζ hζ
    exact (hdiff ζ h1 h2).continuousAt.continuousWithinAt
  · rintro ζ ⟨⟨h1, h2⟩, -⟩
    rw [Metric.mem_ball, dist_zero_right] at h1
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at h2
    exact hdiff ζ h2.le h1.le

/-! Chunk F: one-variable Hartogs step (Cauchy integral in the first variable). -/

def annA (a : ℝ) : Set ℂ := {t : ℂ | a < ‖t‖ ∧ ‖t‖ < 1}

theorem isOpen_annA (a : ℝ) : IsOpen (annA a) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem annA_subset (a : ℝ) : annA a ⊆ Metric.ball 0 1 := fun _ ht => mem_ball_zero_iff.2 ht.2

theorem mem_annA_mid {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (((a + 1) / 2 : ℝ) : ℂ) ∈ annA a := by
  show a < ‖(((a + 1) / 2 : ℝ) : ℂ)‖ ∧ ‖(((a + 1) / 2 : ℝ) : ℂ)‖ < 1
  rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  constructor <;> linarith

theorem isPreconnected_annA {a : ℝ} (ha : 0 ≤ a) : IsPreconnected (annA a) := by
  have : annA a = (fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) '' (Set.Ioo a 1 ×ˢ Set.univ) := by
    ext t
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(‖t‖, arg t), ⟨⟨h1, h2⟩, Set.mem_univ _⟩, norm_mul_exp_arg_mul_I t⟩
    · rintro ⟨⟨r, θ⟩, ⟨⟨h1, h2⟩, -⟩, rfl⟩
      have hr : 0 ≤ r := ha.trans h1.le
      have hn : ‖(r : ℂ) * exp (θ * I)‖ = r := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hr]
      show a < ‖(r : ℂ) * exp (θ * I)‖ ∧ ‖(r : ℂ) * exp (θ * I)‖ < 1
      rw [hn]; exact ⟨h1, h2⟩
  rw [this]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _
    (Continuous.continuousOn (by fun_prop))

theorem step_ext [FiniteDimensional ℂ Y] {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {D B : Set Y} (hD : IsOpen D) (hDc : IsPreconnected D) (hB : IsOpen B) (hBD : B ⊆ D)
    (hBne : B.Nonempty) {f : ℂ × Y → ℂ}
    (hf : DifferentiableOn ℂ f (annA a ×ˢ D ∪ Metric.ball 0 1 ×ˢ B)) :
    ∃ g : ℂ × Y → ℂ, DifferentiableOn ℂ g (Metric.ball 0 1 ×ˢ D) ∧
      EqOn g f (annA a ×ˢ D ∪ Metric.ball 0 1 ×ˢ B) := by
  have hΩ : IsOpen (annA a ×ˢ D ∪ Metric.ball (0:ℂ) 1 ×ˢ B) :=
    ((isOpen_annA a).prod hD).union (Metric.isOpen_ball.prod hB)
  set ρ : ℂ → ℝ := fun ξ => (max a ‖ξ‖ + 1) / 2 with hρ
  have hρa : ∀ ξ : ℂ, a < ρ ξ := fun ξ => by
    simp only [hρ]; linarith [le_max_left a ‖ξ‖]
  have hρ1 : ∀ ξ : ℂ, ‖ξ‖ < 1 → ρ ξ < 1 := fun ξ h => by
    simp only [hρ]; have := max_lt ha1 h; linarith
  have hρξ : ∀ ξ : ℂ, ‖ξ‖ < 1 → ‖ξ‖ < ρ ξ := fun ξ h => by
    simp only [hρ]; linarith [le_max_right a ‖ξ‖]
  set g : ℂ × Y → ℂ := fun x => (2 * π * I : ℂ)⁻¹ • cauchyInt (ρ x.1) f x with hg
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 1 ×ˢ D) := by
    rintro ⟨ξ₀, y₀⟩ ⟨h1, h2⟩
    rw [mem_ball_zero_iff] at h1
    set R := ρ ξ₀ with hR
    have hR0 : 0 < R := ha.trans (hρa _)
    have hcd : DifferentiableOn ℂ (cauchyInt R f) (Metric.ball 0 R ×ˢ D) :=
      differentiableOn_cauchyInt hΩ hf hR0 hD (fun y hy ζ hζ => by
        rw [mem_sphere_zero_iff_norm] at hζ
        exact Or.inl ⟨⟨hζ ▸ hρa _, hζ ▸ hρ1 _ h1⟩, hy⟩)
    have hmem : (ξ₀, y₀) ∈ Metric.ball (0:ℂ) R ×ˢ D :=
      ⟨mem_ball_zero_iff.2 (hρξ _ h1), h2⟩
    have hopen : IsOpen (Metric.ball (0:ℂ) R ×ˢ D) := Metric.isOpen_ball.prod hD
    have hda : DifferentiableAt ℂ (fun x => (2 * π * I : ℂ)⁻¹ • cauchyInt R f x) (ξ₀, y₀) :=
      by
        have := ((hcd _ hmem).differentiableAt (hopen.mem_nhds hmem)).const_smul
          ((2 * π * I : ℂ)⁻¹)
        exact this
    refine (hda.congr_of_eventuallyEq ?_).differentiableWithinAt
    have hev : ∀ᶠ x in 𝓝 (ξ₀, y₀), x ∈ Metric.ball (0:ℂ) R ×ˢ D ∧ x.1 ∈ Metric.ball (0:ℂ) 1 := by
      filter_upwards [hopen.mem_nhds hmem,
        continuous_fst.continuousAt.preimage_mem_nhds
          (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 h1))] with x hx hx'
      exact ⟨hx, hx'⟩
    filter_upwards [hev] with x hx
    obtain ⟨ξ, y⟩ := x
    obtain ⟨⟨hxb, hxD⟩, hx1⟩ := hx
    rw [mem_ball_zero_iff] at hxb hx1
    show (2 * π * I : ℂ)⁻¹ • cauchyInt (ρ ξ) f (ξ, y) = (2 * π * I : ℂ)⁻¹ • cauchyInt R f (ξ, y)
    rcases le_total (ρ ξ) R with hle | hle
    · rw [cauchyInt_eq_of_le hΩ hf (ha.trans (hρa ξ)) hle ?_ (hρξ ξ hx1)]
      intro ζ hz1 hz2
      exact Or.inl ⟨⟨(hρa _).trans_le hz1, hz2.trans_lt (hρ1 _ h1)⟩, hxD⟩
    · rw [cauchyInt_eq_of_le hΩ hf hR0 hle ?_ hxb]
      intro ζ hz1 hz2
      exact Or.inl ⟨⟨(hρa _).trans_le hz1, hz2.trans_lt (hρ1 _ hx1)⟩, hxD⟩
  have hgB : EqOn g f (Metric.ball 0 1 ×ˢ B) := by
    rintro ⟨ξ, y⟩ ⟨h1, h2⟩
    rw [mem_ball_zero_iff] at h1
    have hy : ∀ ζ ∈ Metric.closedBall (0:ℂ) (ρ ξ), (ζ, y) ∈ annA a ×ˢ D ∪ Metric.ball 0 1 ×ˢ B :=
      fun ζ hζ => by
        rw [mem_closedBall_zero_iff] at hζ
        exact Or.inr ⟨mem_ball_zero_iff.2 (hζ.trans_lt (hρ1 ξ h1)), h2⟩
    exact cauchyInt_eq hΩ hf hy (mem_ball_zero_iff.2 (hρξ ξ h1))
  have hAD : EqOn g f (annA a ×ˢ D) := by
    obtain ⟨y₀, hy₀⟩ := hBne
    refine eqOn_of_preconnected_of_open ((isOpen_annA a).prod hD)
      ((isPreconnected_annA ha.le).prod hDc)
      (hgd.mono (Set.prod_mono (annA_subset a) Subset.rfl)) (hf.mono subset_union_left)
      ((isOpen_annA a).prod hB) (Set.prod_mono Subset.rfl hBD)
      ⟨((((a + 1) / 2 : ℝ) : ℂ), y₀), mem_annA_mid ha ha1, hy₀⟩ ?_
    intro x hx
    exact hgB ⟨annA_subset a hx.1, hx.2⟩
  refine ⟨g, hgd, ?_⟩
  rintro x (hx | hx)
  · exact hAD hx
  · exact hgB hx

/-! Chunk G: peel the annulus coordinates one at a time (induction on a Finset). -/

def zs (a : ℝ) {m : ℕ} (J : Finset (Fin m)) (l : Fin m) : Set ℂ :=
  if l ∈ J then annA a else Metric.ball 0 1

theorem zs_sub_ball (a : ℝ) {m : ℕ} (J : Finset (Fin m)) (l : Fin m) :
    zs a J l ⊆ Metric.ball 0 1 := by
  unfold zs; split_ifs
  · exact annA_subset a
  · exact Subset.rfl

theorem zs_insert_self (a : ℝ) {m : ℕ} (J : Finset (Fin m)) (j : Fin m) :
    zs a (insert j J) j = annA a := by
  simp [zs]

theorem zs_insert_of_ne (a : ℝ) {m : ℕ} (J : Finset (Fin m)) {j l : Fin m} (h : l ≠ j) :
    zs a (insert j J) l = zs a J l := by
  simp [zs, h]

theorem zs_mono (a : ℝ) {m : ℕ} {J J' : Finset (Fin m)} (h : J ⊆ J') (l : Fin m) :
    zs a J' l ⊆ zs a J l := by
  intro t ht
  unfold zs at ht ⊢
  by_cases hl : l ∈ J
  · rw [if_pos (h hl)] at ht; rw [if_pos hl]; exact ht
  · rw [if_neg hl]
    split_ifs at ht
    · exact annA_subset a ht
    · exact ht

theorem isOpen_zs (a : ℝ) {m : ℕ} (J : Finset (Fin m)) (l : Fin m) : IsOpen (zs a J l) := by
  unfold zs; split_ifs
  · exact isOpen_annA a
  · exact Metric.isOpen_ball

theorem isPreconnected_zs {a : ℝ} (ha : 0 ≤ a) {m : ℕ} (J : Finset (Fin m)) (l : Fin m) :
    IsPreconnected (zs a J l) := by
  unfold zs; split_ifs
  · exact isPreconnected_annA ha
  · exact (convex_ball _ _).isPreconnected

def Dset (a : ℝ) (m k : ℕ) (J : Finset (Fin m)) : Set ((Fin m → ℂ) × (Fin k → ℂ)) :=
  Set.pi univ (zs a J) ×ˢ Set.pi univ (fun _ : Fin k => Metric.ball (0:ℂ) 1)

def Rset (b : ℝ) (m k : ℕ) : Set ((Fin m → ℂ) × (Fin k → ℂ)) :=
  Set.pi univ (fun _ : Fin m => Metric.ball (0:ℂ) 1) ×ˢ
    Set.pi univ (fun _ : Fin k => Metric.ball (0:ℂ) b)

theorem isOpen_Dset (a : ℝ) (m k : ℕ) (J : Finset (Fin m)) : IsOpen (Dset a m k J) :=
  (isOpen_set_pi Set.finite_univ fun l _ => isOpen_zs a J l).prod
    (isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball)

theorem isOpen_Rset (b : ℝ) (m k : ℕ) : IsOpen (Rset b m k) :=
  (isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball).prod
    (isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball)

theorem isPreconnected_Dset {a : ℝ} (ha : 0 ≤ a) (m k : ℕ) (J : Finset (Fin m)) :
    IsPreconnected (Dset a m k J) :=
  (isPreconnected_univ_pi fun l => isPreconnected_zs ha J l).prod
    (isPreconnected_univ_pi fun _ => (convex_ball _ _).isPreconnected)

theorem Dset_mono (a : ℝ) (m k : ℕ) {J J' : Finset (Fin m)} (h : J ⊆ J') :
    Dset a m k J' ⊆ Dset a m k J :=
  fun _ hx => ⟨fun l _ => zs_mono a h l (hx.1 l (Set.mem_univ _)), hx.2⟩

theorem ext_J {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) {m k : ℕ}
    (J : Finset (Fin m)) :
    ∀ f : (Fin m → ℂ) × (Fin k → ℂ) → ℂ, DifferentiableOn ℂ f (Dset a m k J ∪ Rset b m k) →
      ∃ F : (Fin m → ℂ) × (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F (Dset a m k ∅) ∧
        EqOn F f (Dset a m k J ∪ Rset b m k) := by
  classical
  induction J using Finset.induction_on
  case empty =>
    intro f hf
    exact ⟨f, hf.mono subset_union_left, fun _ _ => rfl⟩
  case insert j J hj ih =>
    intro f hf
    have hBo : IsOpen (Dset a m k J ∩
        (Set.univ ×ˢ Set.pi univ (fun _ : Fin k => Metric.ball (0:ℂ) b))) :=
      (isOpen_Dset a m k J).inter
        (isOpen_univ.prod (isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball))
    have hBne : (Dset a m k J ∩
        (Set.univ ×ˢ Set.pi univ (fun _ : Fin k => Metric.ball (0:ℂ) b))).Nonempty := by
      refine ⟨(fun _ => (((a + 1) / 2 : ℝ) : ℂ), 0),
        ⟨fun l _ => ?_, fun l _ => ?_⟩, Set.mem_univ _, fun l _ => ?_⟩
      · show _ ∈ zs a J l
        unfold zs; split_ifs
        · exact mem_annA_mid ha ha1
        · exact annA_subset a (mem_annA_mid ha ha1)
      · simp
      · simpa using hb
    let φ : ℂ × ((Fin m → ℂ) × (Fin k → ℂ)) → (Fin m → ℂ) × (Fin k → ℂ) :=
      fun p => (fun l => if l = j then p.1 else p.2.1 l, p.2.2)
    have hφd : Differentiable ℂ φ := by
      show Differentiable ℂ (fun p : ℂ × ((Fin m → ℂ) × (Fin k → ℂ)) =>
        ((fun l => if l = j then p.1 else p.2.1 l), p.2.2))
      refine Differentiable.prodMk (differentiable_pi.2 fun l => ?_) (by fun_prop)
      by_cases hl : l = j
      · simp only [if_pos hl]; fun_prop
      · simp only [if_neg hl]; fun_prop
    have hmaps : Set.MapsTo φ (annA a ×ˢ Dset a m k J ∪ Metric.ball 0 1 ×ˢ (Dset a m k J ∩
        (Set.univ ×ˢ Set.pi univ (fun _ : Fin k => Metric.ball (0:ℂ) b))))
        (Dset a m k (insert j J) ∪ Rset b m k) := by
      rintro ⟨t, z, w⟩ (⟨ht, hz, hw⟩ | ⟨ht, ⟨hz, -⟩, -, hwb⟩)
      · left
        refine ⟨fun l _ => ?_, hw⟩
        show (if l = j then t else z l) ∈ zs a (insert j J) l
        by_cases hl : l = j
        · subst hl; rw [if_pos rfl, zs_insert_self]; exact ht
        · rw [if_neg hl, zs_insert_of_ne a J hl]; exact hz l (Set.mem_univ _)
      · right
        refine ⟨fun l _ => ?_, hwb⟩
        show (if l = j then t else z l) ∈ Metric.ball (0:ℂ) 1
        by_cases hl : l = j
        · rw [if_pos hl]; exact ht
        · rw [if_neg hl]; exact zs_sub_ball a J l (hz l (Set.mem_univ _))
    obtain ⟨g, hg, hgf⟩ := step_ext (Y := (Fin m → ℂ) × (Fin k → ℂ)) ha ha1
      (isOpen_Dset a m k J) (isPreconnected_Dset ha.le m k J) hBo Set.inter_subset_left hBne
      (f := f ∘ φ) (hf.comp hφd.differentiableOn hmaps)
    have hφψ : ∀ x : (Fin m → ℂ) × (Fin k → ℂ), φ (x.1 j, x) = x := by
      rintro ⟨z, w⟩
      show ((fun l => if l = j then z j else z l), w) = (z, w)
      congr 1
      funext l
      by_cases hl : l = j
      · rw [if_pos hl, hl]
      · rw [if_neg hl]
    have hψ : ∀ x ∈ Dset a m k J, (x.1 j, x) ∈ Metric.ball (0:ℂ) 1 ×ˢ Dset a m k J :=
      fun x hx => ⟨zs_sub_ball a J j (hx.1 j (Set.mem_univ _)), hx⟩
    let h : (Fin m → ℂ) × (Fin k → ℂ) → ℂ := fun x =>
      if x ∈ Dset a m k J then g (x.1 j, x) else f x
    have hhf : EqOn h f (Dset a m k (insert j J) ∪ Rset b m k) := by
      intro x hx
      show (if x ∈ Dset a m k J then g (x.1 j, x) else f x) = f x
      split_ifs with hxD
      · have hmem : (x.1 j, x) ∈ annA a ×ˢ Dset a m k J ∪ Metric.ball 0 1 ×ˢ (Dset a m k J ∩
            (Set.univ ×ˢ Set.pi univ (fun _ : Fin k => Metric.ball (0:ℂ) b))) := by
          rcases hx with hx | hx
          · left
            have h1 := hx.1 j (Set.mem_univ _)
            rw [zs_insert_self] at h1
            exact ⟨h1, hxD⟩
          · right
            exact ⟨hx.1 j (Set.mem_univ _), hxD, Set.mem_univ _, hx.2⟩
        rw [hgf hmem, Function.comp_apply, hφψ]
      · rfl
    have hHo : IsOpen (Dset a m k (insert j J) ∪ Rset b m k) :=
      (isOpen_Dset a m k _).union (isOpen_Rset b m k)
    have hhd : DifferentiableOn ℂ h (Dset a m k J ∪ Rset b m k) := by
      intro x hx
      by_cases hxD : x ∈ Dset a m k J
      · have hgx : DifferentiableAt ℂ (fun y : (Fin m → ℂ) × (Fin k → ℂ) => g (y.1 j, y)) x := by
          have h1 := (hg _ (hψ x hxD)).differentiableAt
            ((Metric.isOpen_ball.prod (isOpen_Dset a m k J)).mem_nhds (hψ x hxD))
          have h2 : DifferentiableAt ℂ
              (fun y : (Fin m → ℂ) × (Fin k → ℂ) => (y.1 j, y)) x := by fun_prop
          exact DifferentiableAt.comp (f := fun y : (Fin m → ℂ) × (Fin k → ℂ) => (y.1 j, y)) x h1 h2
        refine (hgx.congr_of_eventuallyEq ?_).differentiableWithinAt
        filter_upwards [(isOpen_Dset a m k J).mem_nhds hxD] with y hy
        show (if y ∈ Dset a m k J then g (y.1 j, y) else f y) = g (y.1 j, y)
        rw [if_pos hy]
      · have hxH : x ∈ Dset a m k (insert j J) ∪ Rset b m k := Or.inr (hx.resolve_left hxD)
        refine (((hf x hxH).differentiableAt (hHo.mem_nhds hxH)).congr_of_eventuallyEq
          ?_).differentiableWithinAt
        filter_upwards [hHo.mem_nhds hxH] with y hy
        exact hhf hy
    obtain ⟨F, hF, hFh⟩ := ih h hhd
    refine ⟨F, hF, fun x hx => ?_⟩
    have hxJ : x ∈ Dset a m k J ∪ Rset b m k := by
      rcases hx with hx | hx
      · exact Or.inl (Dset_mono a m k (Finset.subset_insert j J) hx)
      · exact Or.inr hx
    rw [hFh hxJ, hhf hx]

end HFE


/-! fe5a3ef1 tomato can, route v2, chunk 1 (Mathlib only): second-order Peano Taylor bound and
negativity of the defining function along the holomorphic quadratic curve `p + ζ a + ζ² b`. -/

set_option autoImplicit false

open Filter Topology Set Complex

namespace TCChart

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Second-order Taylor bound with uniform little-o remainder at a point where `fderiv f`
is differentiable. -/
theorem taylor2 {f : E → ℝ} {x₀ : E} {s : Set E} (hs : s ∈ 𝓝 x₀)
    (hd : ∀ x ∈ s, HasFDerivAt f (fderiv ℝ f x) x) {f2 : E →L[ℝ] E →L[ℝ] ℝ}
    (h2 : HasFDerivAt (fderiv ℝ f) f2 x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : E, ‖h‖ < δ →
      |f (x₀ + h) - f x₀ - fderiv ℝ f x₀ h - 1 / 2 * f2 h h| ≤ ε * ‖h‖ ^ 2 := by
  have hlo := h2.isLittleO
  obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 ((hlo.def hε).and hs)
  refine ⟨δ, hδ, fun h hh => ?_⟩
  set g : ℝ → ℝ := fun t => f (x₀ + t • h) - t * fderiv ℝ f x₀ h - t * t / 2 * f2 h h with hg
  have hmem : ∀ t ∈ Icc (0:ℝ) 1, dist (x₀ + t • h) x₀ < δ := by
    intro t ht
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg h, ht.2]
  have hder : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt g
      (fderiv ℝ f (x₀ + t • h) h - fderiv ℝ f x₀ h - t * f2 h h) (Icc 0 1) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => x₀ + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x₀
    have h2' := (hd _ (H (hmem t ht)).2).comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t * fderiv ℝ f x₀ h) (fderiv ℝ f x₀ h) t := by
      simpa using (hasDerivAt_id t).mul_const (fderiv ℝ f x₀ h)
    have h4 : HasDerivAt (fun t : ℝ => t * t / 2 * f2 h h) (t * f2 h h) t := by
      have := (((hasDerivAt_id' t).mul (hasDerivAt_id' t)).div_const 2).mul_const (f2 h h)
      exact this.congr_deriv (by ring)
    exact ((h2'.sub h3).sub h4).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0:ℝ) 1,
      ‖fderiv ℝ f (x₀ + t • h) h - fderiv ℝ f x₀ h - t * f2 h h‖ ≤ ε * ‖h‖ ^ 2 := by
    intro t ht
    have hH := (H (hmem t (Ico_subset_Icc_self ht))).1
    simp only [add_sub_cancel_left] at hH
    have he : fderiv ℝ f (x₀ + t • h) h - fderiv ℝ f x₀ h - t * f2 h h =
        (fderiv ℝ f (x₀ + t • h) - fderiv ℝ f x₀ - f2 (t • h)) h := by
      simp [map_smul, smul_eq_mul]
    rw [he]
    have hn : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      nlinarith [norm_nonneg h, ht.2]
    calc _ ≤ ‖fderiv ℝ f (x₀ + t • h) - fderiv ℝ f x₀ - f2 (t • h)‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖t • h‖ * ‖h‖ := by gcongr
      _ ≤ ε * ‖h‖ * ‖h‖ := by gcongr
      _ = ε * ‖h‖ ^ 2 := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hder hbound 1
    (right_mem_Icc.2 zero_le_one)
  have e : g 1 - g 0 = f (x₀ + h) - f x₀ - fderiv ℝ f x₀ h - 1 / 2 * f2 h h := by
    simp only [hg, one_smul, zero_smul, add_zero]
    ring
  rw [e, Real.norm_eq_abs, sub_zero, mul_one] at key
  exact key

end Taylor

section Curve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smul_decomp (c : ℂ) (v : E) : c • v = c.re • v + c.im • (I • v) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- Along the quadratic holomorphic curve `x₀ + ζ a + ζ² b` (suitable `b`), a function with
vanishing value and complex-tangent derivative at `x₀` and negative "Levi" quantity
`A = f''(a,a) + f''(Ia,Ia)` is `≤ (A/8)|ζ|²` near `ζ = 0`. -/
theorem curve_neg {f : E → ℝ} {x₀ : E} {s : Set E} (hs : s ∈ 𝓝 x₀)
    (hd : ∀ x ∈ s, HasFDerivAt f (fderiv ℝ f x) x) {f2 : E →L[ℝ] E →L[ℝ] ℝ}
    (h2 : HasFDerivAt (fderiv ℝ f) f2 x₀) (h0 : f x₀ = 0) {a ν : E}
    (ha : fderiv ℝ f x₀ a = 0) (hia : fderiv ℝ f x₀ (I • a) = 0)
    (hν : fderiv ℝ f x₀ ν = 1) (hiν : fderiv ℝ f x₀ (I • ν) = 0)
    (hA : f2 a a + f2 (I • a) (I • a) < 0) :
    ∃ b : E, ∃ ε > 0, ∀ ζ : ℂ, ‖ζ‖ ≤ ε →
      f (x₀ + ζ • a + ζ ^ 2 • b) ≤ (f2 a a + f2 (I • a) (I • a)) / 8 * ‖ζ‖ ^ 2 := by
  set L := fderiv ℝ f x₀ with hL
  set A := f2 a a + f2 (I • a) (I • a) with hAdef
  set s0 : ℝ := (f2 (I • a) (I • a) - f2 a a) / 4 with hs0
  set t0 : ℝ := (f2 a (I • a) + f2 (I • a) a) / 4 with ht0
  set b : E := ((s0 : ℂ) + t0 * I) • ν with hb
  set K : ℝ := ‖a‖ + ‖b‖ + 1 with hK
  set C : ℝ := ‖f2‖ * (2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2) / 2 + 1 with hC
  have hKpos : 0 < K := by positivity
  have hCpos : 0 < C := by positivity
  have hε' : 0 < -A / (16 * K ^ 2) := div_pos (by linarith) (by positivity)
  obtain ⟨δ, hδ, hT⟩ := taylor2 hs hd h2 hε'
  have hεpos : 0 < min 1 (min (-A / (16 * C)) (δ / (2 * K))) :=
    lt_min one_pos (lt_min (div_pos (by linarith) (by positivity)) (by positivity))
  refine ⟨b, _, hεpos, fun ζ hζ => ?_⟩
  have hζ1 : ‖ζ‖ ≤ 1 := hζ.trans (min_le_left _ _)
  have hζ2 : ‖ζ‖ ≤ -A / (16 * C) := hζ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hζ3 : ‖ζ‖ ≤ δ / (2 * K) := hζ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hz0 := norm_nonneg ζ
  set u : E := ζ • a with hu
  set w : E := ζ ^ 2 • b with hw
  have hun : ‖u‖ = ‖ζ‖ * ‖a‖ := norm_smul _ _
  have hwn : ‖w‖ = ‖ζ‖ ^ 2 * ‖b‖ := by rw [hw, norm_smul, norm_pow]
  have hsq : ‖ζ‖ ^ 2 ≤ ‖ζ‖ := by nlinarith
  have hh : ‖u + w‖ ≤ K * ‖ζ‖ := by
    calc ‖u + w‖ ≤ ‖u‖ + ‖w‖ := norm_add_le _ _
      _ ≤ K * ‖ζ‖ := by
        rw [hun, hwn, hK]
        nlinarith [norm_nonneg a, norm_nonneg b, mul_le_mul_of_nonneg_right hsq (norm_nonneg b)]
  have hKζ : K * ‖ζ‖ < δ := by
    have := mul_le_mul_of_nonneg_left hζ3 hKpos.le
    have h2K : K * (δ / (2 * K)) = δ / 2 := by field_simp
    linarith
  have hT' := hT (u + w) (lt_of_le_of_lt hh hKζ)
  rw [h0] at hT'
  have hgoal : x₀ + ζ • a + ζ ^ 2 • b = x₀ + (u + w) := by rw [add_assoc]
  rw [hgoal]
  have hLu : L u = 0 := by
    rw [hu, smul_decomp, map_add, map_smul, map_smul, ha, hia, smul_zero, smul_zero, add_zero]
  have hLw : L w = (ζ.re ^ 2 - ζ.im ^ 2) * s0 - 2 * ζ.re * ζ.im * t0 := by
    have hre : (ζ ^ 2 * ((s0 : ℂ) + t0 * I)).re
        = (ζ.re ^ 2 - ζ.im ^ 2) * s0 - 2 * ζ.re * ζ.im * t0 := by
      simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hw, hb, smul_smul, smul_decomp, map_add, map_smul, map_smul, hν, hiν, smul_zero,
      add_zero, smul_eq_mul, mul_one, hre]
  have hf2u : f2 u u = ζ.re ^ 2 * f2 a a + ζ.re * ζ.im * (f2 a (I • a) + f2 (I • a) a)
      + ζ.im ^ 2 * f2 (I • a) (I • a) := by
    rw [hu, smul_decomp]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  have hexp : f2 (u + w) (u + w) = f2 u u + (f2 u w + f2 w u + f2 w w) := by
    simp only [map_add, ContinuousLinearMap.add_apply]
    ring
  have hnorm : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hmain : L (u + w) + 1 / 2 * f2 (u + w) (u + w) =
      A / 4 * ‖ζ‖ ^ 2 + (f2 u w + f2 w u + f2 w w) / 2 := by
    rw [map_add, hLu, hLw, hexp, hf2u, hnorm, hs0, ht0, hAdef]
    ring
  have hb2 : ∀ x y : E, |f2 x y| ≤ ‖f2‖ * ‖x‖ * ‖y‖ := by
    intro x y
    rw [← Real.norm_eq_abs]
    exact f2.le_opNorm₂ x y
  have hR : |f2 u w + f2 w u + f2 w w| ≤ ‖f2‖ * (2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2) * ‖ζ‖ ^ 3 := by
    have e1 := hb2 u w
    have e2 := hb2 w u
    have e3 := hb2 w w
    simp only [hun, hwn] at e1 e2 e3
    have hz4 : ‖ζ‖ ^ 4 ≤ ‖ζ‖ ^ 3 := by
      have := pow_le_pow_of_le_one hz0 hζ1 (show 3 ≤ 4 by norm_num)
      exact this
    have hf0 := norm_nonneg f2
    have hb0 := norm_nonneg b
    have ha0 := norm_nonneg a
    calc |f2 u w + f2 w u + f2 w w| ≤ |f2 u w| + |f2 w u| + |f2 w w| := abs_add_three _ _ _
      _ ≤ ‖f2‖ * (‖ζ‖ * ‖a‖) * (‖ζ‖ ^ 2 * ‖b‖) + ‖f2‖ * (‖ζ‖ ^ 2 * ‖b‖) * (‖ζ‖ * ‖a‖)
          + ‖f2‖ * (‖ζ‖ ^ 2 * ‖b‖) * (‖ζ‖ ^ 2 * ‖b‖) := by linarith
      _ = ‖f2‖ * (2 * ‖a‖ * ‖b‖) * ‖ζ‖ ^ 3 + ‖f2‖ * ‖b‖ ^ 2 * ‖ζ‖ ^ 4 := by ring
      _ ≤ ‖f2‖ * (2 * ‖a‖ * ‖b‖) * ‖ζ‖ ^ 3 + ‖f2‖ * ‖b‖ ^ 2 * ‖ζ‖ ^ 3 := by
          gcongr
      _ = _ := by ring
  have hR2 : |f2 u w + f2 w u + f2 w w| / 2 ≤ -A / 16 * ‖ζ‖ ^ 2 := by
    have hC3 : ‖f2‖ * (2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2) / 2 ≤ C := by rw [hC]; linarith
    have hz3 : ‖ζ‖ ^ 3 = ‖ζ‖ * ‖ζ‖ ^ 2 := by ring
    have hCz : C * ‖ζ‖ ≤ -A / 16 := by
      have := mul_le_mul_of_nonneg_left hζ2 hCpos.le
      have e : C * (-A / (16 * C)) = -A / 16 := by field_simp
      linarith
    have hz2 := sq_nonneg ‖ζ‖
    calc |f2 u w + f2 w u + f2 w w| / 2
        ≤ ‖f2‖ * (2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2) / 2 * ‖ζ‖ ^ 3 := by linarith
      _ ≤ C * ‖ζ‖ ^ 3 := by gcongr
      _ = (C * ‖ζ‖) * ‖ζ‖ ^ 2 := by ring
      _ ≤ -A / 16 * ‖ζ‖ ^ 2 := by gcongr
  have herr : ‖u + w‖ ^ 2 ≤ K ^ 2 * ‖ζ‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have herr2 : -A / (16 * K ^ 2) * ‖u + w‖ ^ 2 ≤ -A / 16 * ‖ζ‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left herr hε'.le
    have e : -A / (16 * K ^ 2) * (K ^ 2 * ‖ζ‖ ^ 2) = -A / 16 * ‖ζ‖ ^ 2 := by
      field_simp
    linarith
  have hT2 := (abs_le.1 hT').2
  have hRle := le_abs_self (f2 u w + f2 w u + f2 w w)
  rw [← hL] at hT2
  linarith [hmain]

end Curve

end TCChart


/-! Chunk 3 (session 5): geometry of the tomato can and the extension glue (Mathlib only). -/

namespace TCGeo

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The chart `(ξ, w) ↦ p + (εξ) a + (εξ)² b + w`. -/
noncomputable def chartMap (p a b : E) (ε : ℝ) (x : ℂ × E) : E :=
  p + ((ε : ℂ) * x.1) • a + ((ε : ℂ) * x.1) ^ 2 • b + x.2

theorem differentiable_chartMap (p a b : E) (ε : ℝ) : Differentiable ℂ (chartMap p a b ε) := by
  unfold chartMap
  fun_prop

theorem strict_ball {r : E → ℝ} {p : E} {L : E →L[ℝ] ℝ} (hL : HasStrictFDerivAt r L p)
    {η : ℝ} (hη : 0 < η) : ∃ R > 0, ∀ x ∈ ball p R, ∀ y ∈ ball p R,
      r y ≤ r x + L (y - x) + η * ‖y - x‖ := by
  have h := (hasStrictFDerivAt_iff_isLittleO.1 hL).def hη
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨R, hR, fun x hx y hy => ?_⟩
  have hd : dist (y, x) (p, p) < R := by
    rw [Prod.dist_eq]; exact max_lt hy hx
  have h1 := hball hd
  simp only [Real.norm_eq_abs] at h1
  have h2 := (le_abs_self (r y - r x - L (y - x))).trans h1
  linarith

theorem exists_nu {L : E →L[ℝ] ℝ} (hL : L ≠ 0) : ∃ ν : E, L ν = 1 ∧ L (I • ν) = 0 := by
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra h
    push Not at h
    exact hL (ContinuousLinearMap.ext h)
  set α := L v with hα
  set β := L (I • v) with hβ
  have hpos : 0 < α ^ 2 + β ^ 2 :=
    add_pos_of_pos_of_nonneg (lt_of_le_of_ne (sq_nonneg α) (Ne.symm (pow_ne_zero 2 hv)))
      (sq_nonneg β)
  set s := α ^ 2 + β ^ 2 with hs
  refine ⟨(α / s) • v + (β / s) • (I • v), ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hα, ← hβ,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hpos.ne']
    rw [hs]; ring
  · have hI : I • ((α / s) • v + (β / s) • (I • v)) = (α / s) • (I • v) - (β / s) • v := by
      rw [smul_add, smul_comm I (α / s) v, smul_comm I (β / s) (I • v), smul_smul I I v, I_mul_I,
        neg_one_smul, smul_neg, sub_eq_add_neg]
    rw [hI, map_sub, L.map_smul (α / s) (I • v), L.map_smul (β / s) v, smul_eq_mul, smul_eq_mul,
      ← hα, ← hβ,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div, mul_comm α β, sub_self, zero_div]

set_option maxHeartbeats 1000000 in
theorem geo {U V : Set E} {r : E → ℝ} {p : E}
    (hUV : ∀ x ∈ V, r x < 0 → x ∈ U) (hUr : ∀ x ∈ U, x ∈ V → r x < 0)
    (hVo : IsOpen V) (hpV : p ∈ V)
    {L : E →L[ℝ] ℝ} (hL : HasStrictFDerivAt r L p) {a b ν : E} {ε0 c : ℝ} (hc : 0 < c)
    (hε0 : 0 < ε0)
    (hcurve : ∀ ζ : ℂ, ‖ζ‖ ≤ ε0 → r (p + ζ • a + ζ ^ 2 • b) ≤ -c * ‖ζ‖ ^ 2) (hν : L ν = 1) :
    ∃ ε : ℝ, ∃ D B : Set E, IsOpen D ∧ Convex ℝ D ∧ (0 : E) ∈ D ∧ IsOpen B ∧ B ⊆ D ∧
      B.Nonempty ∧
      (∀ ξ : ℂ, 1 / 2 < ‖ξ‖ → ‖ξ‖ < 1 → ∀ w ∈ D, chartMap p a b ε (ξ, w) ∈ U) ∧
      (∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ w ∈ B, chartMap p a b ε (ξ, w) ∈ U) ∧
      IsPreconnected {x : ℂ × E | x ∈ ball (0 : ℂ) 1 ×ˢ D ∧ chartMap p a b ε x ∈ U} := by
  obtain ⟨η, hηpos, hην, hη8⟩ : ∃ η : ℝ, 0 < η ∧ η * ‖ν‖ ≤ 1 / 8 ∧ η ≤ 1 / 8 := by
    have hk : 0 < ‖ν‖ + 1 := by positivity
    have hX : 0 < 1 / (8 * (‖ν‖ + 1)) := by positivity
    have hXe : 1 / (8 * (‖ν‖ + 1)) * (‖ν‖ + 1) = 1 / 8 := by
      rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) (by norm_num)]; ring
    generalize 1 / (8 * (‖ν‖ + 1)) = X at hX hXe ⊢
    refine ⟨X, hX, ?_, ?_⟩ <;> nlinarith [norm_nonneg ν]
  obtain ⟨R1, hR1, hstrict⟩ := strict_ball hL hηpos
  obtain ⟨R2, hR2, hR2V⟩ := Metric.isOpen_iff.1 hVo p hpV
  set R := min R1 R2 with hRdef
  have hRpos : 0 < R := lt_min hR1 hR2
  have hRV : ball p R ⊆ V := (ball_subset_ball (min_le_right _ _)).trans hR2V
  have hRs : ∀ x ∈ ball p R, ∀ y ∈ ball p R, r y ≤ r x + L (y - x) + η * ‖y - x‖ :=
    fun x hx y hy => hstrict x (ball_subset_ball (min_le_left _ _) hx) y
      (ball_subset_ball (min_le_left _ _) hy)
  set K0 : ℝ := ‖a‖ + ‖b‖ + 1 with hK0def
  have hK0pos : 0 < K0 := by positivity
  set ε : ℝ := min ε0 (min 1 (R / (2 * K0))) with hεdef
  have hεpos : 0 < ε := lt_min hε0 (lt_min one_pos (by positivity))
  have hεε0 : ε ≤ ε0 := min_le_left _ _
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεR : ε * K0 ≤ R / 2 := by
    have h : ε ≤ R / (2 * K0) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  set γ : ℂ → E := fun ξ => p + ((ε : ℂ) * ξ) • a + ((ε : ℂ) * ξ) ^ 2 • b with hγ
  have hn : ∀ ξ : ℂ, ‖(ε : ℂ) * ξ‖ = ε * ‖ξ‖ := fun ξ => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεpos]
  have hγp : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ‖γ ξ - p‖ < R / 2 := by
    intro ξ hξ
    have hz : ‖(ε : ℂ) * ξ‖ ≤ ε := by
      rw [hn]
      have := mul_le_mul_of_nonneg_left hξ hεpos.le
      linarith
    have hz1 : ‖(ε : ℂ) * ξ‖ ≤ 1 := hz.trans hε1
    have hsq : ‖(ε : ℂ) * ξ‖ ^ 2 ≤ ε := by nlinarith [norm_nonneg ((ε : ℂ) * ξ)]
    have he : γ ξ - p = ((ε : ℂ) * ξ) • a + ((ε : ℂ) * ξ) ^ 2 • b := by
      show p + ((ε : ℂ) * ξ) • a + ((ε : ℂ) * ξ) ^ 2 • b - p = _
      abel
    rw [he]
    calc ‖((ε : ℂ) * ξ) • a + ((ε : ℂ) * ξ) ^ 2 • b‖
        ≤ ‖((ε : ℂ) * ξ) • a‖ + ‖((ε : ℂ) * ξ) ^ 2 • b‖ := norm_add_le _ _
      _ = ‖(ε : ℂ) * ξ‖ * ‖a‖ + ‖(ε : ℂ) * ξ‖ ^ 2 * ‖b‖ := by
          rw [norm_smul, norm_smul, norm_pow]
      _ ≤ ε * ‖a‖ + ε * ‖b‖ :=
          add_le_add (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hsq (norm_nonneg _))
      _ < ε * K0 := by rw [hK0def]; nlinarith
      _ ≤ R / 2 := hεR
  have hγr : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → r (γ ξ) ≤ -c * ε ^ 2 * ‖ξ‖ ^ 2 := by
    intro ξ hξ
    have h := hcurve ((ε : ℂ) * ξ) (by
      rw [hn]
      have := mul_le_mul_of_nonneg_left hξ hεpos.le
      linarith)
    rw [hn] at h
    calc r (γ ξ) ≤ -c * (ε * ‖ξ‖) ^ 2 := h
      _ = -c * ε ^ 2 * ‖ξ‖ ^ 2 := by ring
  set Kc : ℝ := c * ε ^ 2 / 4 with hKcdef
  have hKc : 0 < Kc := by positivity
  set σ : ℝ := min (Kc / 2) (R / (4 * (‖ν‖ + 1))) with hσdef
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  have hσK : σ ≤ Kc / 2 := min_le_left _ _
  have hσR : σ * (‖ν‖ + 1) ≤ R / 4 := by
    have h : σ ≤ R / (4 * (‖ν‖ + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  set δ : ℝ := σ / 8 with hδdef
  have hδ : 0 < δ := by positivity
  set πL : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - L.smulRight ν with hπL
  have hπ : ∀ w, πL w = w - L w • ν := fun w => by simp [hπL]
  have hLs : ∀ s : ℝ, L (s • ν) = s := fun s => by rw [map_smul, hν, smul_eq_mul, mul_one]
  have hπν : ∀ s : ℝ, πL (s • ν) = 0 := fun s => by rw [hπ, hLs, sub_self]
  set D : Set E := πL ⁻¹' ball 0 δ ∩ L ⁻¹' Ioo (-σ) σ with hDdef
  set B : Set E := D ∩ L ⁻¹' Iio (-(σ / 2)) with hBdef
  have hmemD : ∀ w, w ∈ D ↔ ‖πL w‖ < δ ∧ -σ < L w ∧ L w < σ := fun w => by
    rw [hDdef]
    simp only [mem_inter_iff, mem_preimage, mem_ball_zero_iff, mem_Ioo]
  have hDo : IsOpen D :=
    (isOpen_ball.preimage πL.continuous).inter (isOpen_Ioo.preimage L.continuous)
  have hDc : Convex ℝ D :=
    ((convex_ball (0 : E) δ).linear_preimage πL.toLinearMap).inter
      ((convex_Ioo (-σ) σ).linear_preimage L.toLinearMap)
  have h0D : (0 : E) ∈ D := by
    rw [hmemD, map_zero, map_zero, norm_zero]
    exact ⟨hδ, by linarith, hσ⟩
  have hBo : IsOpen B := hDo.inter (isOpen_Iio.preimage L.continuous)
  have hBc : Convex ℝ B := hDc.inter ((convex_Iio _).linear_preimage L.toLinearMap)
  have hw0 : (-(3 * σ / 4)) • ν ∈ B := by
    refine ⟨(hmemD _).2 ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hπν, norm_zero]; exact hδ
    · rw [hLs]; linarith
    · rw [hLs]; linarith
    · show L _ < _
      rw [hLs]; linarith
  have hwn : ∀ w ∈ D, ‖w‖ ≤ σ * (‖ν‖ + 1) := by
    intro w hw
    rw [hmemD] at hw
    obtain ⟨h1, h2, h3⟩ := hw
    have he : w = πL w + L w • ν := by rw [hπ]; abel
    have habs : |L w| ≤ σ := abs_le.2 ⟨h2.le, h3.le⟩
    calc ‖w‖ = ‖πL w + L w • ν‖ := by rw [← he]
      _ ≤ ‖πL w‖ + ‖L w • ν‖ := norm_add_le _ _
      _ = ‖πL w‖ + |L w| * ‖ν‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ δ + σ * ‖ν‖ := add_le_add h1.le (mul_le_mul_of_nonneg_right habs (norm_nonneg _))
      _ ≤ σ * (‖ν‖ + 1) := by rw [hδdef]; nlinarith
  have hηw : ∀ w ∈ D, η * ‖w‖ ≤ σ / 4 := by
    intro w hw
    have h1 := mul_le_mul_of_nonneg_left (hwn w hw) hηpos.le
    nlinarith [mul_le_mul_of_nonneg_left hην hσ.le, mul_le_mul_of_nonneg_left hη8 hσ.le]
  have hball1 : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → γ ξ ∈ ball p R := fun ξ hξ => by
    rw [mem_ball, dist_eq_norm]; linarith [hγp ξ hξ]
  have hball2 : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ∀ w ∈ D, γ ξ + w ∈ ball p R := by
    intro ξ hξ w hw
    rw [mem_ball, dist_eq_norm]
    have he : γ ξ + w - p = (γ ξ - p) + w := by abel
    rw [he]
    have h1 := hγp ξ hξ
    have h2 := hwn w hw
    calc ‖(γ ξ - p) + w‖ ≤ ‖γ ξ - p‖ + ‖w‖ := norm_add_le _ _
      _ < R := by linarith
  have hrw : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ∀ w ∈ D, r (γ ξ + w) ≤ r (γ ξ) + L w + σ / 4 := by
    intro ξ hξ w hw
    have h := hRs _ (hball1 ξ hξ) _ (hball2 ξ hξ w hw)
    rw [add_sub_cancel_left] at h
    linarith [hηw w hw]
  have hUmem : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ∀ w ∈ D, r (γ ξ + w) < 0 →
      chartMap p a b ε (ξ, w) ∈ U :=
    fun ξ hξ w hw hr => hUV _ (hRV (hball2 ξ hξ w hw)) hr
  have hann : ∀ ξ : ℂ, 1 / 2 < ‖ξ‖ → ‖ξ‖ < 1 → ∀ w ∈ D, chartMap p a b ε (ξ, w) ∈ U := by
    intro ξ h1 h2 w hw
    refine hUmem ξ h2.le w hw ?_
    have hq : (1 / 2 : ℝ) ^ 2 ≤ ‖ξ‖ ^ 2 := by nlinarith [norm_nonneg ξ]
    have hγ' := hγr ξ h2.le
    have hLw : L w < σ := ((hmemD w).1 hw).2.2
    have hce : 0 ≤ c * ε ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left hq hce
    have h4 := hrw ξ h2.le w hw
    linarith
  have hdisc : ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ w ∈ B, chartMap p a b ε (ξ, w) ∈ U := by
    intro ξ h2 w hw
    refine hUmem ξ h2.le w hw.1 ?_
    have hγ' := hγr ξ h2.le
    have hce : 0 ≤ c * ε ^ 2 * ‖ξ‖ ^ 2 := by positivity
    have h4 := hrw ξ h2.le w hw.1
    have hLw : L w < -(σ / 2) := hw.2
    linarith
  have hS : IsPreconnected {x : ℂ × E | x ∈ ball (0 : ℂ) 1 ×ˢ D ∧ chartMap p a b ε x ∈ U} := by
    have hPB : IsPreconnected (ball (0 : ℂ) 1 ×ˢ B) :=
      ((convex_ball (0 : ℂ) 1).prod hBc).isPreconnected
    have hPBS : ball (0 : ℂ) 1 ×ˢ B ⊆
        {x : ℂ × E | x ∈ ball (0 : ℂ) 1 ×ˢ D ∧ chartMap p a b ε x ∈ U} := by
      rintro ⟨ξ, w⟩ ⟨hξ, hw⟩
      exact ⟨⟨hξ, hw.1⟩, hdisc ξ (mem_ball_zero_iff.1 hξ) w hw⟩
    refine isPreconnected_of_forall ((0 : ℂ), (-(3 * σ / 4)) • ν) ?_
    rintro ⟨ξ, w⟩ ⟨⟨hξ, hw⟩, hU⟩
    have hξ1 : ‖ξ‖ < 1 := mem_ball_zero_iff.1 hξ
    set T : ℝ := max 0 (L w + 3 * σ / 4) with hTdef
    have hT0 : 0 ≤ T := le_max_left _ _
    have hT1 : L w + 3 * σ / 4 ≤ T := le_max_right _ _
    obtain ⟨hπw, hLw1, hLw2⟩ := (hmemD w).1 hw
    have hr0 : r (γ ξ + w) < 0 := hUr _ hU (hRV (hball2 ξ hξ1.le w hw))
    have hseg : ∀ s ∈ Icc (0 : ℝ) T, w - s • ν ∈ D ∧ chartMap p a b ε (ξ, w - s • ν) ∈ U := by
      rintro s ⟨hs0, hsT⟩
      have hLws : L (w - s • ν) = L w - s := by rw [map_sub, hLs]
      have hπws : πL (w - s • ν) = πL w := by rw [map_sub, hπν, sub_zero]
      have hlow : -σ < L w - s := by
        rcases le_total 0 (L w + 3 * σ / 4) with h | h
        · rw [hTdef, max_eq_right h] at hsT; linarith
        · rw [hTdef, max_eq_left h] at hsT; linarith
      have hD' : w - s • ν ∈ D := (hmemD _).2
        ⟨by rw [hπws]; exact hπw, by rw [hLws]; exact hlow, by rw [hLws]; linarith⟩
      refine ⟨hD', hUmem ξ hξ1.le _ hD' ?_⟩
      have h := hRs _ (hball2 ξ hξ1.le w hw) _ (hball2 ξ hξ1.le _ hD')
      have he : γ ξ + (w - s • ν) - (γ ξ + w) = -(s • ν) := by abel
      rw [he, map_neg, hLs, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0] at h
      have h5 := mul_le_mul_of_nonneg_left hην hs0
      nlinarith
    refine ⟨(fun s : ℝ => ((ξ, w - s • ν) : ℂ × E)) '' Icc 0 T ∪ ball (0 : ℂ) 1 ×ˢ B,
      ?_, ?_, ?_, ?_⟩
    · rintro x (⟨s, hs, rfl⟩ | hx)
      · exact ⟨⟨hξ, (hseg s hs).1⟩, (hseg s hs).2⟩
      · exact hPBS hx
    · right; exact ⟨mem_ball_self one_pos, hw0⟩
    · left; exact ⟨0, ⟨le_rfl, hT0⟩, by simp⟩
    · refine IsPreconnected.union (ξ, w - T • ν) ⟨T, ⟨hT0, le_rfl⟩, rfl⟩ ⟨hξ, ?_⟩ ?_ hPB
      · refine ⟨(hseg T ⟨hT0, le_rfl⟩).1, ?_⟩
        show L _ < _
        rw [map_sub, hLs]; linarith
      · exact isPreconnected_Icc.image _
          (by fun_prop : Continuous fun s : ℝ => ((ξ, w - s • ν) : ℂ × E)).continuousOn
  exact ⟨ε, D, B, hDo, hDc, h0D, hBo, inter_subset_left, ⟨_, hw0⟩, hann, hdisc, hS⟩

theorem ext_of_geo [FiniteDimensional ℂ E] {U : Set E} (hUo : IsOpen U) {p a b : E} {ε : ℝ}
    {D B : Set E} (hDo : IsOpen D) (hDc : Convex ℝ D) (h0D : (0 : E) ∈ D) (hBo : IsOpen B)
    (hBD : B ⊆ D) (hBne : B.Nonempty)
    (hann : ∀ ξ : ℂ, 1 / 2 < ‖ξ‖ → ‖ξ‖ < 1 → ∀ w ∈ D, chartMap p a b ε (ξ, w) ∈ U)
    (hdisc : ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ w ∈ B, chartMap p a b ε (ξ, w) ∈ U)
    (hS : IsPreconnected {x : ℂ × E | x ∈ ball (0 : ℂ) 1 ×ˢ D ∧ chartMap p a b ε x ∈ U}) :
    ∃ W : Set E, IsOpen W ∧ IsConnected W ∧ p ∈ W ∧
      ∀ f : E → ℂ, DifferentiableOn ℂ f U →
        ∃ F : E → ℂ, DifferentiableOn ℂ F W ∧ Set.EqOn F f (U ∩ W) := by
  have hΦd := differentiable_chartMap p a b ε
  set S : Set (ℂ × E) := {x : ℂ × E | x ∈ ball (0 : ℂ) 1 ×ˢ D ∧ chartMap p a b ε x ∈ U}
    with hSdef
  have hSo : IsOpen S := (isOpen_ball.prod hDo).inter (hUo.preimage hΦd.continuous)
  have hWo : IsOpen ((fun x : E => x - p) ⁻¹' D) := hDo.preimage (by fun_prop)
  have hpW : p ∈ (fun x : E => x - p) ⁻¹' D := by simpa using h0D
  refine ⟨(fun x : E => x - p) ⁻¹' D, hWo, ⟨⟨p, hpW⟩, ?_⟩, hpW, ?_⟩
  · have he : (fun x : E => x - p) ⁻¹' D = (fun w : E => w + p) '' D := by
      ext x
      constructor
      · intro hx
        exact ⟨x - p, hx, sub_add_cancel x p⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [he]
    exact hDc.isPreconnected.image _ (by fun_prop : Continuous fun w : E => w + p).continuousOn
  intro f hf
  have hH : DifferentiableOn ℂ (f ∘ chartMap p a b ε)
      (HFE.annA (1 / 2) ×ˢ D ∪ ball (0 : ℂ) 1 ×ˢ B) := by
    refine hf.comp hΦd.differentiableOn ?_
    rintro ⟨ξ, w⟩ (⟨⟨h1, h2⟩, hw⟩ | ⟨hξ, hw⟩)
    · exact hann ξ h1 h2 w hw
    · exact hdisc ξ (mem_ball_zero_iff.1 hξ) w hw
  obtain ⟨g, hg, hgeq⟩ := HFE.step_ext (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hDo
    hDc.isPreconnected hBo hBD hBne hH
  have hfS : DifferentiableOn ℂ (f ∘ chartMap p a b ε) S :=
    hf.comp hΦd.differentiableOn (fun x hx => hx.2)
  have hgS : DifferentiableOn ℂ g S := hg.mono (fun x hx => hx.1)
  obtain ⟨w0, hw0⟩ := hBne
  have hEq : EqOn g (f ∘ chartMap p a b ε) S := by
    refine HFE.eqOn_of_preconnected_of_open hSo hS hgS hfS (isOpen_ball.prod hBo) ?_
      ⟨((0 : ℂ), w0), mem_ball_self one_pos, hw0⟩ (fun x hx => hgeq (Or.inr hx))
    rintro ⟨ξ, w⟩ ⟨hξ, hw⟩
    exact ⟨⟨hξ, hBD hw⟩, hdisc ξ (mem_ball_zero_iff.1 hξ) w hw⟩
  refine ⟨fun x => g ((0 : ℂ), x - p), ?_, ?_⟩
  · have hd : Differentiable ℂ (fun x : E => ((0 : ℂ), x - p)) := by fun_prop
    exact hg.comp hd.differentiableOn (fun x hx => ⟨mem_ball_self one_pos, hx⟩)
  · rintro x ⟨hxU, hxW⟩
    have hc : chartMap p a b ε ((0 : ℂ), x - p) = x := by simp [chartMap]
    have hmem : ((0 : ℂ), x - p) ∈ S := ⟨⟨mem_ball_self one_pos, hxW⟩, by rw [hc]; exact hxU⟩
    have h := hEq hmem
    rw [Function.comp_apply, hc] at h
    exact h

end TCGeo



set_option autoImplicit false

namespace TomatoCan

/-- Second conjunct of the tomato can principle from the first: a local extension across a
boundary point of an open set rules out being a domain of holomorphy (take `V = U ∩ W`). -/
theorem not_doh_of_ext {n : ℕ} {U : Set (Fin n → ℂ)} (hUo : IsOpen U) {p : Fin n → ℂ}
    (hp : p ∈ frontier U) {W : Set (Fin n → ℂ)} (hWo : IsOpen W) (hWc : IsConnected W)
    (hpW : p ∈ W)
    (hext : ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f U →
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ Set.EqOn F f (U ∩ W)) :
    ¬ LeblSCV.Shared.IsDomainOfHolomorphy U := by
  rintro ⟨-, -, hno⟩
  apply hno
  have hpU : p ∉ U := by
    rw [hUo.frontier_eq] at hp
    exact hp.2
  refine ⟨U ∩ W, W, hUo.inter hWo, ?_, hWo, hWc, subset_rfl, ?_, ?_⟩
  · have hcl : p ∈ closure U := frontier_subset_closure hp
    obtain ⟨x, hxW, hxU⟩ := (mem_closure_iff.1 hcl) W hWo hpW
    exact ⟨x, hxU, hxW⟩
  · intro hsub
    exact hpU (hsub hpW)
  · intro f hf
    obtain ⟨F, hF, hEq⟩ := hext f hf
    exact ⟨F, hF, fun z hz => (hEq hz).symm⟩

/-- Assembly: the whole statement follows from its first conjunct. -/
theorem of_core {n : ℕ} (U : Set (Fin n → ℂ)) (hU : LeblSCV.Levi.HasSmoothBoundary U)
    (p : Fin n → ℂ) (hp : p ∈ frontier U)
    (hcore : ∃ W : Set (Fin n → ℂ), IsOpen W ∧ IsConnected W ∧ p ∈ W ∧
      ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f U →
        ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ Set.EqOn F f (U ∩ W)) :
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ IsConnected W ∧ p ∈ W ∧
      ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f U →
        ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ Set.EqOn F f (U ∩ W)) ∧
    (IsConnected U → ¬ LeblSCV.Shared.IsDomainOfHolomorphy U) := by
  refine ⟨hcore, fun _ => ?_⟩
  obtain ⟨W, hWo, hWc, hpW, hext⟩ := hcore
  exact not_doh_of_ext hU.1 hp hWo hWc hpW hext

/-- On the defining-function neighbourhood, `U ∩ V = {r < 0} ∩ V`. -/
theorem inter_eq {n : ℕ} {U : Set (Fin n → ℂ)} (hUo : IsOpen U) {p : Fin n → ℂ}
    {V : Set (Fin n → ℂ)} {r : (Fin n → ℂ) → ℝ} (hr : LeblSCV.Levi.IsDefiningFunction U p V r) :
    U ∩ V = {x | x ∈ V ∧ r x < 0} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, hr.neg_of_mem x hx⟩
  · rintro ⟨hxV, hrx⟩
    refine ⟨?_, hxV⟩
    by_contra hxU
    by_cases hcl : x ∈ closure U
    · have hfr : x ∈ frontier U := by
        rw [hUo.frontier_eq]; exact ⟨hcl, hxU⟩
      have : x ∈ frontier U ∩ V := ⟨hfr, hxV⟩
      rw [hr.frontier_inter] at this
      exact absurd this.2 (ne_of_lt hrx)
    · exact absurd (hr.pos_of_not_mem_closure x hxV hcl) (not_lt.2 hrx.le)

end TomatoCan


/-! fe5a3ef1 chunk 2: bridges from the Wirtinger-coordinate Definitions to real derivatives. -/

set_option autoImplicit false

open Filter Topology Set Complex LeblSCV.Levi

namespace TCBridge

variable {n : ℕ}

abbrev eR (k : Fin n) : Fin n → ℂ := Pi.single k 1
abbrev eI (k : Fin n) : Fin n → ℂ := Pi.single k I

theorem vec_expand (v : Fin n → ℂ) : v = ∑ k, ((v k).re • eR k + (v k).im • eI k) := by
  calc v = ∑ k, Pi.single k (v k) := (Finset.univ_sum_single v).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun k _ => ?_
      ext j
      by_cases h : j = k
      · subst h
        simp [Complex.real_smul, Complex.re_add_im]
      · simp [h]

theorem clm_expand (M : (Fin n → ℂ) →L[ℝ] ℝ) (v : Fin n → ℂ) :
    M v = ∑ k, ((v k).re * M (eR k) + (v k).im * M (eI k)) := by
  conv_lhs => rw [vec_expand v]
  simp only [map_sum, map_add, map_smul, smul_eq_mul]

theorem bil_expand (B : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) :
    B u v = ∑ k, ∑ l, ((u k).re * (v l).re * B (eR k) (eR l) + (u k).re * (v l).im * B (eR k) (eI l)
      + (u k).im * (v l).re * B (eI k) (eR l) + (u k).im * (v l).im * B (eI k) (eI l)) := by
  rw [clm_expand (B u) v]
  have hB : ∀ w, B u w = ∑ k, ((u k).re * B (eR k) w + (u k).im * B (eI k) w) := by
    intro w
    have := clm_expand (B.flip w) u
    simpa only [ContinuousLinearMap.flip_apply] using this
  simp only [hB, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem fderiv_ofReal {r : (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : DifferentiableAt ℝ r z) :
    fderiv ℝ (fun x => (r x : ℂ)) z = ofRealCLM.comp (fderiv ℝ r z) :=
  (ofRealCLM.hasFDerivAt.comp z h.hasFDerivAt).fderiv

theorem wZ_eq {r : (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : DifferentiableAt ℝ r z) (l : Fin n) :
    wirtingerZ (fun x => (r x : ℂ)) l z =
      1 / 2 * ((fderiv ℝ r z (eR l) : ℂ) - I * (fderiv ℝ r z (eI l) : ℂ)) := by
  unfold wirtingerZ
  rw [fderiv_ofReal h]
  simp

/-- `a ∈ T^{1,0}`: the real derivative kills `a` and `I • a`. -/
theorem holT {r : (Fin n → ℂ) → ℝ} {p : Fin n → ℂ} (h : DifferentiableAt ℝ r p)
    {a : Fin n → ℂ} (ha : a ∈ holTangent r p) :
    fderiv ℝ r p a = 0 ∧ fderiv ℝ r p (I • a) = 0 := by
  have hs : ∑ k, a k * wirtingerZ (fun z => (r z : ℂ)) k p = 0 := ha
  simp only [wZ_eq h] at hs
  set X : Fin n → ℝ := fun k => fderiv ℝ r p (eR k) with hX
  set Y : Fin n → ℝ := fun k => fderiv ℝ r p (eI k) with hY
  have hs2 : ∑ k, a k * ((X k : ℂ) - I * (Y k : ℂ)) = 0 := by
    have e : ∑ k, a k * (1 / 2 * ((X k : ℂ) - I * (Y k : ℂ)))
        = 1 / 2 * ∑ k, a k * ((X k : ℂ) - I * (Y k : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hs' : ∑ k, a k * (1 / 2 * ((X k : ℂ) - I * (Y k : ℂ))) = 0 := hs
    rw [e] at hs'
    simpa using hs'
  have h1 := congrArg Complex.re hs2
  have h2 := congrArg Complex.im hs2
  simp only [Complex.re_sum, Complex.im_sum, Complex.zero_re, Complex.zero_im] at h1 h2
  constructor
  · rw [clm_expand, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_re, hX, hY]
  · rw [clm_expand, ← neg_zero, ← h2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_re, Complex.mul_im, hX, hY]

theorem levi_re {r : (Fin n → ℂ) → ℝ} {p : Fin n → ℂ}
    {D2 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ}
    (hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ r z) (hD2 : HasFDerivAt (fderiv ℝ r) D2 p)
    (a : Fin n → ℂ) : (leviForm r p a).re = (D2 a a + D2 (I • a) (I • a)) / 4 := by
  have hG : ∀ v : Fin n → ℂ,
      HasFDerivAt (fun z => (fderiv ℝ r z v : ℂ)) (ofRealCLM.comp (D2.flip v)) p := by
    intro v
    have h1 : HasFDerivAt (fun z => fderiv ℝ r z v) (D2.flip v) p := by
      have := hD2.clm_apply (hasFDerivAt_const v p)
      simpa using this
    exact ofRealCLM.hasFDerivAt.comp p h1
  have hW : ∀ l, HasFDerivAt (wirtingerZ (fun x => (r x : ℂ)) l)
      ((1 / 2 : ℂ) • (ofRealCLM.comp (D2.flip (eR l)) - I • ofRealCLM.comp (D2.flip (eI l)))) p := by
    intro l
    have hev : wirtingerZ (fun x => (r x : ℂ)) l =ᶠ[𝓝 p]
        fun z => (1 / 2 : ℂ) • ((fderiv ℝ r z (eR l) : ℂ) - I • (fderiv ℝ r z (eI l) : ℂ)) := by
      filter_upwards [hdiff] with z hz
      rw [wZ_eq hz]
      simp [smul_eq_mul]
    exact (((hG (eR l)).sub ((hG (eI l)).const_smul I)).const_smul (1 / 2 : ℂ)).congr_of_eventuallyEq
      hev
  have hCH : ∀ k l, complexHessian r p k l = 1 / 4 * ((D2 (eR k) (eR l) : ℂ)
      + D2 (eI k) (eI l) + I * ((D2 (eI k) (eR l) : ℂ) - D2 (eR k) (eI l))) := by
    intro k l
    simp only [complexHessian, wirtingerZbar, (hW l).fderiv, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    linear_combination (-(1 / 4 : ℂ) * (D2 (eI k) (eI l) : ℂ)) * I_sq
  rw [leviForm]
  simp only [hCH, Complex.re_sum]
  rw [bil_expand D2 a a, bil_expand D2 (I • a) (I • a), ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

end TCBridge


namespace TomatoCan

open scoped ContDiff in
theorem core {n : ℕ} (U : Set (Fin n → ℂ)) (hU : LeblSCV.Levi.HasSmoothBoundary U)
    (p : Fin n → ℂ) (hp : p ∈ frontier U)
    (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ) (hr : LeblSCV.Levi.IsDefiningFunction U p V r)
    (hneg : ∃ a ∈ LeblSCV.Levi.holTangent r p, (LeblSCV.Levi.leviForm r p a).re < 0) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧ IsConnected W ∧ p ∈ W ∧
      ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f U →
        ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ Set.EqOn F f (U ∩ W) := by
  obtain ⟨a, ha, hlev⟩ := hneg
  have hcd : ContDiffAt ℝ ∞ r p := hr.smooth.contDiffAt (hr.isOpen.mem_nhds hr.mem)
  have hL : HasStrictFDerivAt r (fderiv ℝ r p) p := hcd.hasStrictFDerivAt (by simp)
  have h2 : HasFDerivAt (fderiv ℝ r) (fderiv ℝ (fderiv ℝ r) p) p :=
    ((hcd.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.2 le_top)).differentiableAt
      (by simp)).hasFDerivAt
  have hd : ∀ x ∈ V, HasFDerivAt r (fderiv ℝ r x) x := fun x hx =>
    ((hr.smooth.contDiffAt (hr.isOpen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ r z :=
    Filter.eventually_of_mem (hr.isOpen.mem_nhds hr.mem) (fun x hx => (hd x hx).differentiableAt)
  obtain ⟨hLa, hLIa⟩ := TCBridge.holT hL.hasFDerivAt.differentiableAt ha
  have hre := TCBridge.levi_re hdiff h2 a
  have hA : fderiv ℝ (fderiv ℝ r) p a a
      + fderiv ℝ (fderiv ℝ r) p (Complex.I • a) (Complex.I • a) < 0 := by
    rw [hre] at hlev; linarith
  obtain ⟨ν, hν, hIν⟩ := TCGeo.exists_nu (hr.fderiv_ne_zero p hr.mem)
  have hr0 : r p = 0 := by
    have h : p ∈ frontier U ∩ V := ⟨hp, hr.mem⟩
    rw [hr.frontier_inter] at h
    exact h.2
  obtain ⟨b, ε0, hε0, hcurve⟩ :=
    TCChart.curve_neg (hr.isOpen.mem_nhds hr.mem) hd h2 hr0 hLa hLIa hν hIν hA
  have hUV : ∀ x ∈ V, r x < 0 → x ∈ U := by
    intro x hx hrx
    have h : x ∈ U ∩ V := by rw [TomatoCan.inter_eq hU.1 hr]; exact ⟨hx, hrx⟩
    exact h.1
  have hUr : ∀ x ∈ U, x ∈ V → r x < 0 := fun x hxU hxV => hr.neg_of_mem x ⟨hxU, hxV⟩
  obtain ⟨ε, D, B, hDo, hDc, h0D, hBo, hBD, hBne, hann, hdisc, hS⟩ :=
    TCGeo.geo (a := a) (b := b) (ν := ν) (c := -(fderiv ℝ (fderiv ℝ r) p a a
      + fderiv ℝ (fderiv ℝ r) p (Complex.I • a) (Complex.I • a)) / 8)
      hUV hUr hr.isOpen hr.mem hL (by linarith) hε0
      (fun ζ hζ => by have := hcurve ζ hζ; linarith) hν
  exact TCGeo.ext_of_geo hU.1 hDo hDc h0D hBo hBD hBne hann hdisc hS

end TomatoCan

open LeblSCV.Levi in
theorem solution {n : ℕ} (U : Set (Fin n → ℂ)) (hU : HasSmoothBoundary U)
    (p : Fin n → ℂ) (hp : p ∈ frontier U)
    (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ) (hr : IsDefiningFunction U p V r)
    (hneg : ∃ a ∈ holTangent r p, (leviForm r p a).re < 0) :
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ IsConnected W ∧ p ∈ W ∧
      ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f U →
        ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ Set.EqOn F f (U ∩ W)) ∧
    (IsConnected U → ¬ LeblSCV.Shared.IsDomainOfHolomorphy U) := by
  exact TomatoCan.of_core U hU p hp (TomatoCan.core U hU p hp V r hr hneg)
