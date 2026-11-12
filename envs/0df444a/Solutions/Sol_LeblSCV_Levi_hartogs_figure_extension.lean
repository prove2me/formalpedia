-- Prove2me | solution 1 for LeblSCV.Levi.hartogs_figure_extension
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T16:03:31.192614+00:00
-- url     : https://prove2.me/submissions/a7db5a3a-cf9e-40d6-89fc-165aeea3fa16

import Mathlib
import Definitions.Def_LeblSCV_Levi_unitPolydiscProd
import Definitions.Def_LeblSCV_Levi_hartogsFigure

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

theorem hfe_sets {m k : ℕ} {a b : ℝ} (hb1 : b < 1) :
    LeblSCV.Levi.hartogsFigure m k a b = HFE.Dset a m k Finset.univ ∪ HFE.Rset b m k ∧
    LeblSCV.Levi.unitPolydiscProd m k = HFE.Dset a m k ∅ := by
  constructor
  · ext x
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · left
        refine ⟨fun l _ => ?_, fun l _ => mem_ball_zero_iff.2 (h2 l)⟩
        show x.1 l ∈ HFE.zs a Finset.univ l
        rw [HFE.zs, if_pos (Finset.mem_univ l)]
        exact ⟨h3 l, h1 l⟩
      · right
        exact ⟨fun l _ => mem_ball_zero_iff.2 (h1 l), fun l _ => mem_ball_zero_iff.2 (h3 l)⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        have h1' : ∀ l, x.1 l ∈ HFE.annA a := fun l => by
          have := h1 l (Set.mem_univ _)
          rwa [HFE.zs, if_pos (Finset.mem_univ l)] at this
        exact ⟨⟨fun l => (h1' l).2, fun l => mem_ball_zero_iff.1 (h2 l (Set.mem_univ _))⟩,
          fun l => (h1' l).1⟩
      · right
        refine ⟨⟨fun l => mem_ball_zero_iff.1 (h1 l (Set.mem_univ _)), fun l => ?_⟩,
          fun l => mem_ball_zero_iff.1 (h2 l (Set.mem_univ _))⟩
        exact (mem_ball_zero_iff.1 (h2 l (Set.mem_univ _))).trans hb1
  · ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun l _ => ?_, fun l _ => mem_ball_zero_iff.2 (h2 l)⟩
      show x.1 l ∈ HFE.zs a ∅ l
      rw [HFE.zs, if_neg (by simp)]
      exact mem_ball_zero_iff.2 (h1 l)
    · rintro ⟨h1, h2⟩
      refine ⟨fun l => ?_, fun l => mem_ball_zero_iff.1 (h2 l (Set.mem_univ _))⟩
      have := h1 l (Set.mem_univ _)
      rw [HFE.zs, if_neg (by simp)] at this
      exact mem_ball_zero_iff.1 this

open LeblSCV.Levi in
theorem solution {m k : ℕ} (a b : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) (f : (Fin m → ℂ) × (Fin k → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (hartogsFigure m k a b)) :
    ∃ F : (Fin m → ℂ) × (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F (unitPolydiscProd m k) ∧
      Set.EqOn F f (hartogsFigure m k a b) := by
  obtain ⟨h1, h2⟩ := hfe_sets (m := m) (k := k) (a := a) hb1
  rw [h1] at hf ⊢
  rw [h2]
  exact HFE.ext_J ha ha1 hb Finset.univ f hf
