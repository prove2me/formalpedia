-- Prove2me | solution 1 for MasulloRH.compact_convolution_rigidity_for_log_band_riesz_weight
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T20:02:41.401859+00:00
-- url     : https://prove2.me/submissions/69fc7494-05c2-4c36-a844-3cfaf2eceb2e

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace ConvRigidityAux

open Real Complex Filter Topology FourierTransform

/-- The Fourier–Laplace transform of a continuous compactly supported function is entire. -/
lemma entire (h : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h) :
    Differentiable ℂ (fun ζ : ℂ => ∫ y : ℝ, Complex.exp (-2 * π * I * y * ζ) * h y) := by
  intro ζ₀
  obtain ⟨R, hR⟩ := hhc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hy : ∀ y : ℝ, h y ≠ 0 → |y| ≤ R := by
    intro y hy
    have := hR (subset_tsupport h hy)
    simpa using this
  have hR0 : 0 ≤ R ∨ ∀ y, h y = 0 := by
    by_cases hR0 : 0 ≤ R
    · exact Or.inl hR0
    · right
      intro y
      by_contra hne
      exact hR0 ((abs_nonneg y).trans (hy y hne))
  set C : ℝ := Real.exp (2 * π * |R| * (‖ζ₀‖ + 1)) * (2 * π * |R|) with hC
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
    (F := fun (ζ : ℂ) (y : ℝ) => Complex.exp (-2 * π * I * y * ζ) * h y)
    (F' := fun (ζ : ℂ) (y : ℝ) => Complex.exp (-2 * π * I * y * ζ) * (-2 * π * I * y) * h y)
    (x₀ := ζ₀) (s := Metric.ball ζ₀ 1) (bound := fun y => C * ‖h y‖)
    (Metric.ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt
  · refine Eventually.of_forall fun ζ => ?_
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hhc.mul_left
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall fun y ζ hζ => ?_
    by_cases h0 : h y = 0
    · simp [h0]
    have hyR : |y| ≤ |R| := (hy y h0).trans (le_abs_self R)
    have hζ' : ‖ζ‖ ≤ ‖ζ₀‖ + 1 := by
      have : ‖ζ - ζ₀‖ < 1 := by simpa [dist_eq_norm] using hζ
      calc ‖ζ‖ = ‖ζ₀ + (ζ - ζ₀)‖ := by ring_nf
        _ ≤ ‖ζ₀‖ + ‖ζ - ζ₀‖ := norm_add_le _ _
        _ ≤ ‖ζ₀‖ + 1 := by linarith
    have h1 : ‖(-2 * π * I * y : ℂ)‖ ≤ 2 * π * |R| := by
      have : ‖(-2 * π * I * y : ℂ)‖ = 2 * π * |y| := by
        simp [abs_of_pos Real.pi_pos]
      rw [this]
      have := Real.pi_pos
      gcongr
    have h2 : ‖Complex.exp (-2 * π * I * y * ζ)‖ ≤ Real.exp (2 * π * |R| * (‖ζ₀‖ + 1)) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      calc (-2 * π * I * y * ζ : ℂ).re ≤ ‖(-2 * π * I * y * ζ : ℂ)‖ := Complex.re_le_norm _
        _ = ‖(-2 * π * I * y : ℂ)‖ * ‖ζ‖ := norm_mul _ _
        _ ≤ (2 * π * |R|) * (‖ζ₀‖ + 1) := by
          have := Real.pi_pos
          gcongr
    calc ‖Complex.exp (-2 * π * I * y * ζ) * (-2 * π * I * y) * h y‖
        = ‖Complex.exp (-2 * π * I * y * ζ)‖ * ‖(-2 * π * I * y : ℂ)‖ * ‖h y‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ Real.exp (2 * π * |R| * (‖ζ₀‖ + 1)) * (2 * π * |R|) * ‖h y‖ := by
          gcongr
  · exact (hh.norm.integrable_of_hasCompactSupport hhc.norm).const_mul C
  · refine Eventually.of_forall fun y ζ _ => ?_
    have := (((hasDerivAt_id ζ).const_mul (-2 * π * I * y : ℂ)).cexp).mul_const (h y)
    simpa using this

lemma fourier_eqL (h : ℝ → ℂ) (ξ : ℝ) :
    𝓕 h ξ = ∫ y : ℝ, Complex.exp (-2 * π * I * y * (ξ : ℂ)) * h y := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1
  ext y
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

lemma fourier_cont (g : ℝ → ℂ) (hg : Integrable g) : Continuous (𝓕 g) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hg

lemma fourier_smul' (m : ℂ) (g : ℝ → ℂ) (ξ : ℝ) : 𝓕 (m • g) ξ = m * 𝓕 g ξ := by
  rw [fourier_eqL, fourier_eqL, ← integral_const_mul]
  congr 1
  ext y
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma fourierInv_zero' : 𝓕⁻ (0 : ℝ → ℂ) = 0 := by
  ext ξ
  rw [Real.fourierInv_eq]
  simp

end ConvRigidityAux

open ConvRigidityAux Real Complex Filter Topology FourierTransform Convolution in
theorem solution (α : ℝ) (hα : 0 ≤ α) (h : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h) :
    let w : ℝ → ℝ := fun x : ℝ => Real.exp (2 * α * |x|) * (1 + x^2)^2
    let b : ℝ → ℂ := fun x : ℝ => (w x : ℂ) * ∫ y : ℝ, h y / (w (x-y) : ℂ)
    (∃ m : ℂ, ∀ x : ℝ, b x = m) → h = 0 := by
  intro w b ⟨m, hm⟩
  have hw1 : ∀ x, 1 + x ^ 2 ≤ w x := by
    intro x
    have h1 : 1 ≤ Real.exp (2 * α * |x|) := Real.one_le_exp (by positivity)
    have h2 : (1 : ℝ) ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    show 1 + x ^ 2 ≤ Real.exp (2 * α * |x|) * (1 + x^2)^2
    nlinarith [mul_le_mul h1 (by nlinarith : 1 + x ^ 2 ≤ (1 + x ^ 2) ^ 2) (by positivity)
      (by positivity : (0:ℝ) ≤ Real.exp (2 * α * |x|))]
  have hwpos : ∀ x, 0 < w x := fun x => lt_of_lt_of_le (by positivity) (hw1 x)
  have hwcont : Continuous w := by fun_prop
  set gC : ℝ → ℂ := fun x => ((w x : ℝ) : ℂ)⁻¹ with hgC
  have hgcont : Continuous gC := by
    refine Continuous.inv₀ (by fun_prop) fun x => ?_
    exact_mod_cast (hwpos x).ne'
  have hgint : Integrable gC := by
    have hr : Integrable (fun x => (w x)⁻¹) := by
      refine Integrable.mono' integrable_inv_one_add_sq
        (hwcont.inv₀ fun x => (hwpos x).ne').aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hwpos x))]
      exact inv_anti₀ (by positivity) (hw1 x)
    have := hr.ofReal (𝕜 := ℂ)
    simpa [hgC] using this
  have hhint : Integrable h := hh.integrable_of_hasCompactSupport hhc
  have hconv : (h ⋆[ContinuousLinearMap.mul ℂ ℂ] gC) = m • gC := by
    ext x
    rw [convolution_def]
    have := hm x
    simp only [b] at this
    have hx : ((w x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hwpos x).ne'
    simp only [ContinuousLinearMap.mul_apply', Pi.smul_apply, smul_eq_mul, hgC, ← div_eq_mul_inv]
    rw [← this]
    field_simp
  have hF : ∀ ξ : ℝ, 𝓕 h ξ * 𝓕 gC ξ = m * 𝓕 gC ξ := by
    intro ξ
    rw [← Real.fourier_mul_convolution_eq hhint hgint ξ, hconv, fourier_smul']
  set H : ℂ → ℂ := fun ζ => ∫ y : ℝ, Complex.exp (-2 * π * I * y * ζ) * h y with hH
  have hHd : Differentiable ℂ H := entire h hh hhc
  have hHF : ∀ ξ : ℝ, H ξ = 𝓕 h ξ := fun ξ => (fourier_eqL h ξ).symm
  have hHan : AnalyticOnNhd ℂ (fun ζ => H ζ - m) Set.univ :=
    (hHd.sub_const m).differentiableOn.analyticOnNhd isOpen_univ
  -- H ≡ m
  have hHm : ∀ ζ, H ζ = m := by
    by_contra hne
    have hgF : ∀ ξ₀ : ℝ, 𝓕 gC ξ₀ = 0 := by
      intro ξ₀
      have hnf : ¬ ∃ᶠ z in 𝓝[≠] (ξ₀ : ℂ), (fun ζ => H ζ - m) z = 0 := by
        intro hfr
        apply hne
        intro ζ
        have := hHan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
          (Set.mem_univ _) hfr (Set.mem_univ ζ)
        simpa [sub_eq_zero] using this
      rw [not_frequently] at hnf
      have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] ξ₀) (𝓝[≠] (ξ₀ : ℂ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
      have hev : ∀ᶠ x in 𝓝[≠] ξ₀, 𝓕 gC x = 0 := by
        filter_upwards [htend.eventually hnf] with x hx
        have h1 := hF x
        have h2 : (𝓕 h x - m) * 𝓕 gC x = 0 := by rw [sub_mul, h1, sub_self]
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd (by rw [hHF]; exact h3) hx
        · exact h3
      have hc : Tendsto (𝓕 gC) (𝓝[≠] ξ₀) (𝓝 (𝓕 gC ξ₀)) :=
        (fourier_cont gC hgint).continuousAt.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique hc (tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm))
    have hFg0 : 𝓕 gC = 0 := funext hgF
    have hinv := hgcont.fourierInv_fourier_eq hgint (by rw [hFg0]; exact integrable_zero _ _ _)
    rw [hFg0, fourierInv_zero'] at hinv
    have h0 := congrFun hinv 0
    have hx : ((w 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hwpos 0).ne'
    simp only [Pi.zero_apply, hgC] at h0
    exact inv_ne_zero hx h0.symm
  have hFh : ∀ ξ : ℝ, 𝓕 h ξ = m := fun ξ => by rw [← hHF, hHm]
  have hm0 : m = 0 := by
    have h1 : Tendsto (𝓕 h) (cocompact ℝ) (𝓝 0) := Real.zero_at_infty_fourier h
    have h2 : Tendsto (𝓕 h) (cocompact ℝ) (𝓝 m) :=
      tendsto_const_nhds.congr fun ξ => (hFh ξ).symm
    exact tendsto_nhds_unique h2 h1
  have hFh0 : 𝓕 h = 0 := funext fun ξ => by rw [hFh, hm0]; rfl
  have hinv := hh.fourierInv_fourier_eq hhint (by rw [hFh0]; exact integrable_zero _ _ _)
  rw [hFh0, fourierInv_zero'] at hinv
  exact hinv.symm
