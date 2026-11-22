-- Prove2me | solution 1 for HardyHalfPlane.paleyWiener_laplace_memLeftHardy_two
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T19:13:00.894653+00:00
-- url     : https://prove2.me/submissions/b49d8b55-d106-423e-a98a-4df0becdd78b

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false


open FourierTransform in
open scoped ContDiff in
theorem hardy_fourier_ae_eq (g : ℝ → ℂ) (h1 : Integrable g) (h2 : MemLp g 2) :
    ⇑(𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume] 𝓕 g := by
  have hc : Continuous (𝓕 g) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ h1
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  · exact hc.locallyIntegrable
  · intro φ hφ hφc
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
    set ψ : SchwartzMap ℝ ℂ := hg₁.toSchwartzMap hg₂
    have e1 : ∫ x, φ x • (𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) x =
        Lp.toTemperedDistribution (𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) ψ := by
      rw [Lp.toTemperedDistribution_apply]
      congr 1
    rw [e1, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
      Lp.toTemperedDistribution_apply]
    have e2 : ∫ x, (𝓕 ψ) x • (h2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) x = ∫ x, (𝓕 ψ) x • g x := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with x hx
      rw [hx]
    rw [e2]
    have e3 := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) (μ := volume) (ν := volume)
      Real.continuous_fourierChar continuous_inner ψ.integrable h1
    have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
      ext; simp
    rw [hflip] at e3
    rw [SchwartzMap.fourier_coe]
    convert e3 using 1
    · rfl
    · congr 1

open FourierTransform in
theorem hardy_plancherel (g : ℝ → ℂ) (h1 : Integrable g) (h2 : MemLp g 2) :
    eLpNorm (𝓕 g) 2 volume = eLpNorm g 2 volume := by
  rw [← eLpNorm_congr_ae (hardy_fourier_ae_eq g h1 h2), ← Lp.enorm_def,
    ← eLpNorm_congr_ae h2.coeFn_toLp, ← Lp.enorm_def]
  have := Lp.norm_fourier_eq (h2.toLp g)
  rw [← ofReal_norm, ← ofReal_norm, this]


open Real in
theorem hardy_scale (G : ℝ → ℂ) (hG : Continuous G) :
    eLpNorm (fun y : ℝ => G (-(2 * π)⁻¹ * y)) 2 volume =
      ENNReal.ofReal (Real.sqrt (2 * π)) * eLpNorm G 2 volume := by
  have hc : (-(2 * π)⁻¹ : ℝ) ≠ 0 := by
    have : 0 < 2 * π := by positivity
    simp
  have h1 : (fun y : ℝ => G (-(2 * π)⁻¹ * y)) = G ∘ (fun y : ℝ => -(2 * π)⁻¹ * y) := rfl
  rw [h1, ← eLpNorm_map_measure hG.aestronglyMeasurable (measurable_const_mul _).aemeasurable,
    Real.map_volume_mul_left hc, eLpNorm_smul_measure_of_ne_top (by norm_num), smul_eq_mul]
  congr 1
  have h2 : |(-(2 * π)⁻¹ : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity)]
  rw [h2, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]
  norm_num



open Real FourierTransform in
theorem hardy_line (f : ℝ → ℂ) (σ y : ℝ) :
    (∫ x : ℝ, f x * Complex.exp (((σ : ℂ) + (y : ℂ) * Complex.I) * x)) =
      𝓕 (fun x : ℝ => f x * Complex.exp ((σ : ℂ) * x)) (-(2 * π)⁻¹ * y) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext x
  rw [smul_eq_mul]
  have : ((σ : ℂ) + (y : ℂ) * Complex.I) * x = (σ : ℂ) * x + ((-2 * π * x * (-(2 * π)⁻¹ * y) : ℝ) : ℂ) * Complex.I := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  rw [this, Complex.exp_add]
  ring

theorem hardy_sup (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hf0 : ∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0) :
    (⨆ σ : ℝ, ⨆ _ : σ < 0, eLpNorm (fun x : ℝ => f x * Complex.exp ((σ : ℂ) * x)) 2 volume) =
      eLpNorm f 2 volume := by
  apply le_antisymm
  · refine iSup₂_le fun σ hσ => ?_
    apply eLpNorm_mono_ae
    filter_upwards [hf0] with x hx
    by_cases h : 0 ≤ x
    · rw [norm_mul, Complex.norm_exp]
      have : Real.exp ((σ : ℂ) * x).re ≤ 1 := by
        rw [Real.exp_le_one_iff]
        simp only [← Complex.ofReal_mul, Complex.ofReal_re]
        exact mul_nonpos_of_nonpos_of_nonneg hσ.le h
      calc ‖f x‖ * Real.exp ((σ : ℂ) * x).re ≤ ‖f x‖ * 1 := by gcongr
        _ = ‖f x‖ := mul_one _
    · simp [hx (lt_of_not_ge h)]
  · have hlim := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) (μ := volume)
      (f := fun (n : ℕ) (x : ℝ) => f x * Complex.exp (((-1 / ((n : ℝ) + 1) : ℝ) : ℂ) * x))
      (fun n => hf.1.mul (by fun_prop)) f ?_
    · refine hlim.trans ?_
      apply Filter.liminf_le_of_frequently_le'
      apply Filter.Frequently.of_forall
      intro n
      refine le_iSup₂_of_le (-1 / ((n : ℝ) + 1)) ?_ le_rfl
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_neg_of_neg_of_pos (by norm_num) this
    · refine Filter.Eventually.of_forall fun x => ?_
      have h1 : Filter.Tendsto (fun n : ℕ => (-1 / ((n : ℝ) + 1) : ℝ)) Filter.atTop (nhds 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
        simpa [neg_div] using this
      have h2 : Filter.Tendsto (fun n : ℕ => f x * Complex.exp (((-1 / ((n : ℝ) + 1) : ℝ) : ℂ) * x))
          Filter.atTop (nhds (f x * Complex.exp (((0 : ℝ) : ℂ) * x))) := by
        apply Filter.Tendsto.const_mul
        apply (Complex.continuous_exp.tendsto _).comp
        apply Filter.Tendsto.mul_const
        exact (Complex.continuous_ofReal.tendsto _).comp h1
      simpa using h2


theorem hardy_int_mul (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hf0 : ∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0) (w : ℝ → ℂ) (hwm : AEStronglyMeasurable w volume)
    (hw : Integrable (fun x => ‖w x‖ ^ 2) (volume.restrict (Set.Ici 0))) :
    Integrable (fun x => f x * w x) volume := by
  have h1 : MemLp ((Set.Ici (0:ℝ)).indicator w) 2 volume := by
    rw [memLp_indicator_iff_restrict measurableSet_Ici]
    exact (memLp_two_iff_integrable_sq_norm hwm.restrict).2 hw
  have := hf.integrable_mul h1
  refine this.congr ?_
  filter_upwards [hf0] with x hx
  by_cases h : 0 ≤ x
  · simp [Set.indicator_of_mem, h]
  · simp [hx (lt_of_not_ge h)]

theorem hardy_exp_sq_int (a : ℝ) (ha : a < 0) :
    Integrable (fun x : ℝ => ‖Complex.exp ((a : ℂ) * x)‖ ^ 2) (volume.restrict (Set.Ici 0)) := by
  have : (fun x : ℝ => ‖Complex.exp ((a : ℂ) * x)‖ ^ 2) = fun x => Real.exp ((2 * a) * x) := by
    funext x
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    congr 1
    simp; ring
  rw [this]
  exact (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_mul_Ioi (by linarith) 0)

theorem hardy_int (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hf0 : ∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0) (s : ℂ) (hs : s.re < 0) :
    Integrable (fun x : ℝ => f x * Complex.exp (s * x)) volume := by
  apply hardy_int_mul f hf hf0 _ (by fun_prop)
  have : (fun x : ℝ => ‖Complex.exp (s * x)‖ ^ 2) = fun x : ℝ => ‖Complex.exp ((s.re : ℂ) * x)‖ ^ 2 := by
    funext x; simp [Complex.norm_exp]
  rw [this]
  exact hardy_exp_sq_int _ hs

theorem hardy_holo (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hf0 : ∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x : ℝ, f x * Complex.exp (s * x)) {s : ℂ | s.re < 0} := by
  intro s0 hs0
  replace hs0 : s0.re < 0 := hs0
  apply DifferentiableAt.differentiableWithinAt
  set τ : ℝ := s0.re / 2 with hτ
  have hτ0 : τ < 0 := by linarith
  have hbi : Integrable (fun x : ℝ => ‖f x‖ * (|x| * Real.exp (τ * x))) volume := by
    have := (hardy_int_mul f hf hf0 (fun x => ((|x| * Real.exp (τ * x) : ℝ) : ℂ))
      (by fun_prop) ?_).norm
    · refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (Real.exp_pos _), abs_abs]
    · have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1) (b := -2 * τ)
        (by norm_num) (by norm_num) (by linarith)
      refine (integrableOn_Ici_iff_integrableOn_Ioi).2 (h1.congr_fun (fun x hx => ?_) measurableSet_Ioi)
      simp only [Set.mem_Ioi] at hx
      simp only [Complex.norm_real, Real.norm_eq_abs, Real.rpow_one]
      rw [abs_of_nonneg (by positivity), mul_pow, sq_abs, ← Real.exp_nat_mul]
      rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      congr 2
      push_cast; ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (s := {z : ℂ | z.re < τ}) (x₀ := s0)
    (F := fun s x => f x * Complex.exp (s * x))
    (F' := fun s x => f x * (Complex.exp (s * x) * x))
    (bound := fun x => ‖f x‖ * (|x| * Real.exp (τ * x)))
    ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by simp; linarith))
    (Filter.Eventually.of_forall fun s => hf.1.mul (by fun_prop))
    (hardy_int f hf hf0 s0 hs0) (hf.1.mul (by fun_prop)) ?_ hbi ?_
  · exact key.2.differentiableAt
  · filter_upwards [hf0] with x hx
    intro s hs
    replace hs : s.re < τ := hs
    by_cases h : 0 ≤ x
    · rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        mul_comm (Real.exp _)]
      gcongr
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right hs.le h
    · simp [hx (lt_of_not_ge h)]
  · refine Filter.Eventually.of_forall fun x s _ => ?_
    exact ((hasDerivAt_mul_const (x : ℂ)).cexp).const_mul (f x)

open Real FourierTransform in
theorem solution (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hf0 : ∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0) :
    (∀ s : ℂ, s.re < 0 → Integrable (fun x : ℝ => f x * Complex.exp (s * x)) volume) ∧
    HardyHalfPlane.MemLeftHardy (fun s : ℂ => ∫ x : ℝ, f x * Complex.exp (s * x)) 0 2 ∧
    HardyHalfPlane.leftHardyNorm (fun s : ℂ => ∫ x : ℝ, f x * Complex.exp (s * x)) 0 2 =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi)) * eLpNorm f 2 volume := by
  have hline : ∀ σ : ℝ, σ < 0 →
      eLpNorm (fun y : ℝ => ∫ x : ℝ, f x * Complex.exp (((σ : ℂ) + (y : ℂ) * Complex.I) * x)) 2
        volume = ENNReal.ofReal (Real.sqrt (2 * π)) *
          eLpNorm (fun x : ℝ => f x * Complex.exp ((σ : ℂ) * x)) 2 volume := by
    intro σ hσ
    have hi : Integrable (fun x : ℝ => f x * Complex.exp ((σ : ℂ) * x)) volume :=
      hardy_int f hf hf0 σ (by simpa using hσ)
    have hm : MemLp (fun x : ℝ => f x * Complex.exp ((σ : ℂ) * x)) 2 volume := by
      refine hf.of_le (hf.1.mul (by fun_prop)) ?_
      filter_upwards [hf0] with x hx
      by_cases h : 0 ≤ x
      · rw [norm_mul, Complex.norm_exp]
        have : Real.exp ((σ : ℂ) * x).re ≤ 1 := by
          rw [Real.exp_le_one_iff]
          simp only [← Complex.ofReal_mul, Complex.ofReal_re]
          exact mul_nonpos_of_nonpos_of_nonneg hσ.le h
        calc ‖f x‖ * Real.exp ((σ : ℂ) * x).re ≤ ‖f x‖ * 1 := by gcongr
          _ = ‖f x‖ := mul_one _
      · simp [hx (lt_of_not_ge h)]
    have hc : Continuous (𝓕 (fun x : ℝ => f x * Complex.exp ((σ : ℂ) * x))) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hi
    simp_rw [hardy_line f σ]
    rw [hardy_scale _ hc, hardy_plancherel _ hi hm]
  have hnorm : HardyHalfPlane.leftHardyNorm (fun s : ℂ => ∫ x : ℝ, f x * Complex.exp (s * x)) 0 2 =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi)) * eLpNorm f 2 volume := by
    unfold HardyHalfPlane.leftHardyNorm
    calc (⨆ σ : ℝ, ⨆ _ : σ < 0, eLpNorm (fun y : ℝ =>
          ∫ x : ℝ, f x * Complex.exp (((σ : ℂ) + (y : ℂ) * Complex.I) * x)) 2 volume)
        = ⨆ σ : ℝ, ⨆ _ : σ < 0, ENNReal.ofReal (Real.sqrt (2 * π)) *
          eLpNorm (fun x : ℝ => f x * Complex.exp ((σ : ℂ) * x)) 2 volume := by
          refine iSup_congr fun σ => iSup_congr fun hσ => hline σ hσ
      _ = ENNReal.ofReal (Real.sqrt (2 * π)) * ⨆ σ : ℝ, ⨆ _ : σ < 0,
          eLpNorm (fun x : ℝ => f x * Complex.exp ((σ : ℂ) * x)) 2 volume := by
          simp_rw [ENNReal.mul_iSup]
      _ = _ := by rw [hardy_sup f hf hf0]
  refine ⟨hardy_int f hf hf0, ⟨hardy_holo f hf hf0, ?_⟩, hnorm⟩
  rw [hnorm]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2
