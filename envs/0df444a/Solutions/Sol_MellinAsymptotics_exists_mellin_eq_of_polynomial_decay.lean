-- Prove2me | solution 1 for MellinAsymptotics.exists_mellin_eq_of_polynomial_decay
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:55:32.831841+00:00
-- url     : https://prove2.me/submissions/25b3f2da-d70e-43ab-827f-721935ab7644

import Mathlib

open MeasureTheory Filter Topology Asymptotics

set_option autoImplicit false

namespace Sol_MellinAsymptotics_exists_mellin_eq_of_polynomial_decay

open Function Set
open scoped ContDiff ENNReal FourierTransform NNReal Interval

local notation "verticalPoint" =>
  (fun (σ y : ℝ) ↦ (σ : ℂ) + (y : ℂ) * Complex.I)
local notation "verticalTrace" =>
  (fun (Φ : ℂ → ℂ) (σ : ℝ) (y : ℝ) ↦ Φ (verticalPoint σ y))
local notation "atAbsInfty" => (comap abs atTop)
local notation "logWeight" =>
  (fun (σ x : ℝ) ↦ (Real.exp (σ * x) : ℂ))

/-- An upward vertical line integral. -/
noncomputable def verticalLineIntegral (Φ : ℂ → ℂ) (σ : ℝ) : ℂ :=
  Complex.I * ∫ y : ℝ, Φ (verticalPoint σ y)

/-- Change of variables `t = exp x` for integrability on `(0, ∞)`. -/
theorem integrable_comp_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    Integrable (fun x : ℝ ↦ Real.exp x • g (Real.exp x)) ↔ IntegrableOn g (Ioi 0) := by
  rw [← Real.range_exp, ← image_univ,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    integrableOn_univ]
  simp only [abs_of_pos (Real.exp_pos _)]

/-- A logarithmic profile has an absolutely convergent Mellin integral at `s` if its
exponential weight at the real part of `s` is integrable on the real line. -/
theorem mellinConvergent_of_integrable_logWeight (f : ℝ → ℂ) (s : ℂ)
    (h : Integrable (fun x : ℝ ↦ (Real.exp (s.re * x) : ℂ) * f x)) :
    MellinConvergent (fun t ↦ f (Real.log t)) s := by
  let phase (x : ℝ) := Complex.exp ((x : ℂ) * (s - s.re))
  have hc : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hunit (x : ℝ) : ‖phase x‖ ≤ 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re]
  apply (integrable_comp_exp _).mp
  apply (h.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hunit)).congr
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [phase, Complex.ofReal_exp, Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Cauchy–Goursat on expanding rectangles allows a vertical contour to be shifted
across a strip of holomorphy when its horizontal boundary integrals tend to zero. -/
theorem verticalIntegral_eq_of_contour_shift {K : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hK : DifferentiableOn ℂ K (Complex.re ⁻¹' Icc c d))
    (hc : Complex.VerticalIntegrable K c) (hd : Complex.VerticalIntegrable K d)
    (hh : Tendsto (fun y : ℝ ↦ ∫ x in c..d, K (verticalPoint x y)) atAbsInfty (𝓝 0)) :
    verticalLineIntegral K d = verticalLineIntegral K c := by
  have hrect (t : ℝ) :
      (∫ x in c..d, K (verticalPoint x (-t))) - (∫ x in c..d, K (verticalPoint x t)) +
      Complex.I • (∫ y in -t..t, K (verticalPoint d y)) -
      Complex.I • (∫ y in -t..t, K (verticalPoint c y)) = 0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn K (⟨c, -t⟩ : ℂ) (⟨d, t⟩ : ℂ)
    apply hK.mono
    intro w hw
    simpa only [uIcc_of_le hcd] using hw.1
  have ht : Tendsto (fun t : ℝ ↦ t) atTop atAbsInfty := by
    apply tendsto_comap_iff.mpr
    exact tendsto_abs_atTop_atTop
  have hn : Tendsto (fun t : ℝ ↦ -t) atTop atAbsInfty := by
    apply tendsto_comap_iff.mpr
    simpa [Function.comp_def] using tendsto_abs_atTop_atTop
  have hv (x : ℝ) (hi : Complex.VerticalIntegrable K x) :=
    intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot
      (tendsto_id : Tendsto id atTop (atTop : Filter ℝ))
  have hlim := (((hh.comp hn).sub (hh.comp ht)).add ((hv d hd).const_smul Complex.I)).sub
    ((hv c hc).const_smul Complex.I)
  have heq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun t ↦ (hrect t).symm)
  simpa [verticalLineIntegral, sub_eq_zero] using heq

/-- A weighted bound on a closed strip, together with continuity on the strip,
gives uniform polynomial decay in the height. -/
theorem verticalTrace_polynomialDecay {F : ℂ → ℂ} {c d N C₀ : ℝ} (hN : 0 ≤ N)
    (hF : ContinuousOn F (Complex.re ⁻¹' Icc c d))
    (hBound : ∀ s : ℂ, c ≤ s.re → s.re ≤ d → ‖s‖ ^ N * ‖F s‖ ≤ C₀) :
    ∃ C ≥ (0 : ℝ), ∀ σ ∈ Icc c d, ∀ y : ℝ,
      ‖verticalTrace F σ y‖ ≤ C * (1 + ‖y‖) ^ (-N) := by
  have hK : IsCompact (Icc c d ×ˢ Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ ↦ F (verticalPoint p.1 p.2))
      (Icc c d ×ˢ Icc (-1 : ℝ) 1) := by
    refine hF.comp (by fun_prop) ?_
    intro p hp
    simpa using hp.1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  refine ⟨2 ^ N * max (max C₀ M) 0, by positivity, ?_⟩
  intro σ hσ y
  let z := verticalPoint σ y
  have hpos : 0 < (1 + ‖y‖) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]
  by_cases hy : |y| ≤ 1
  · have hFz : ‖F z‖ ≤ M := hM (σ, y) ⟨hσ, abs_le.mp hy⟩
    have h1 : (1 + ‖y‖) ^ N ≤ 2 ^ N := by
      apply Real.rpow_le_rpow (by positivity) _ hN
      rw [Real.norm_eq_abs]; linarith
    calc ‖F z‖ * (1 + ‖y‖) ^ N ≤ max (max C₀ M) 0 * 2 ^ N := by
          apply mul_le_mul _ h1 hpos.le (by positivity)
          exact hFz.trans ((le_max_right C₀ M).trans (le_max_left _ _))
      _ = 2 ^ N * max (max C₀ M) 0 := mul_comm _ _
  · push Not at hy
    have him : ‖y‖ ≤ ‖z‖ := by simpa [z, Real.norm_eq_abs] using Complex.abs_im_le_norm z
    have hle : 1 + ‖y‖ ≤ 2 * ‖z‖ := by
      rw [Real.norm_eq_abs] at him ⊢; linarith
    have hz := hBound z (by simpa [z] using hσ.1) (by simpa [z] using hσ.2)
    calc
      ‖F z‖ * (1 + ‖y‖) ^ N ≤ ‖F z‖ * (2 * ‖z‖) ^ N := by
        gcongr
      _ = 2 ^ N * (‖z‖ ^ N * ‖F z‖) := by
        rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (hz.trans ((le_max_left C₀ M).trans (le_max_left _ _))) h2.le

/-- An integrable power envelope controls every moment whose remaining decay has exponent
greater than one. -/
theorem integrable_verticalTrace_moment {f : ℝ → ℂ} (hf : Continuous f)
    {C N : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C * (1 + ‖y‖) ^ (-N))
    (j : ℕ) (hj : (j : ℝ) < N - 1) :
    Integrable (fun y : ℝ ↦ y ^ j • f y) := by
  have hmodel : Integrable (fun y : ℝ ↦ (1 + ‖y‖) ^ (-(N - (j : ℝ)))) :=
    integrable_one_add_norm (by simpa using (show 1 < N - (j : ℝ) by linarith))
  apply (hmodel.const_mul C).mono' (by fun_prop)
  filter_upwards with y
  rw [norm_smul]
  calc
    ‖y ^ j‖ * ‖f y‖ ≤ (1 + ‖y‖) ^ j * (C * (1 + ‖y‖) ^ (-N)) := by
      rw [norm_pow]
      gcongr
      · exact le_add_of_nonneg_left zero_le_one
      · exact hbound y
    _ = C * (1 + ‖y‖) ^ (-(N - (j : ℝ))) := by
      rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add (by positivity)]
      congr 2
      ring

/-- The inverse Mellin integral agrees on either side of a closed strip when the
vertical traces are integrable and have uniform power decay with exponent at least one. -/
theorem mellinInv_eq_of_verticalTrace_decay {F : ℂ → ℂ} {c d C N : ℝ}
    (hcd : c ≤ d) (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc c d))
    (hc : Complex.VerticalIntegrable F c) (hd : Complex.VerticalIntegrable F d)
    (hC : 0 ≤ C) (hN : 1 ≤ N)
    (hdecay : ∀ σ ∈ Icc c d, ∀ y : ℝ, ‖verticalTrace F σ y‖ ≤ C * (1 + ‖y‖) ^ (-N))
    {t : ℝ} (ht : 0 < t) : mellinInv c F t = mellinInv d F t := by
  let P (s : ℂ) := (t : ℂ) ^ (-s)
  let K (s : ℂ) := P s * F s
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hP : Differentiable ℂ P := differentiable_id.neg.const_cpow (.inl ht0)
  have hnorm (σ y : ℝ) : ‖P (verticalPoint σ y)‖ = t ^ (-σ) := by
    simp [P, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hi (σ : ℝ) (h : Complex.VerticalIntegrable F σ) : Complex.VerticalIntegrable K σ := by
    have hcont : Continuous (verticalTrace P σ) := hP.continuous.comp (by fun_prop)
    exact h.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ (hnorm σ y).le)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := c) (b := d)).bddAbove_image
    ((Real.continuous_const_rpow ht.ne').comp continuous_neg).continuousOn
  have hh : Tendsto (fun y : ℝ ↦ ∫ x in c..d, K (verticalPoint x y)) atAbsInfty (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards with y
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro σ hσ
      have hσ' := Ioc_subset_Icc_self ((uIoc_of_le hcd) ▸ hσ)
      have hb : t ^ (-σ) ≤ B := hB (mem_image_of_mem _ hσ')
      have hpow : (1 + ‖y‖) ^ (-N) ≤ (1 + ‖y‖)⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le (by simp) (by linarith)
      change ‖P (verticalPoint σ y) * F (verticalPoint σ y)‖ ≤ _
      rw [norm_mul, hnorm, mul_comm (t ^ (-σ))]
      calc
        _ ≤ (C * (1 + ‖y‖) ^ (-N)) * t ^ (-σ) :=
          mul_le_mul_of_nonneg_right (hdecay σ hσ' y) (by positivity)
        _ ≤ (C * (1 + ‖y‖)⁻¹) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) hb (by positivity) (by positivity)
        _ = C * B / (1 + ‖y‖) := by ring
    · have hy : Tendsto (fun y : ℝ ↦ 1 + ‖y‖) atAbsInfty atTop := by
        simpa only [Real.norm_eq_abs] using
          tendsto_atTop_add_const_left atAbsInfty (1 : ℝ) (tendsto_comap :
            Tendsto (abs : ℝ → ℝ) atAbsInfty atTop)
      simpa only [zero_mul] using
        (((tendsto_const_nhds (x := C * B)).div_atTop hy).mul_const |d - c|)
  have heq := verticalIntegral_eq_of_contour_shift hcd (hP.differentiableOn.mul hF)
    (hi c hc) (hi d hd) hh
  unfold verticalLineIntegral at heq
  exact congrArg ((1 / (2 * Real.pi)) • ·) (mul_left_cancel₀ Complex.I_ne_zero heq).symm

/-- In logarithmic coordinates the normalized inverse Mellin integral is the
Fourier transform of the appropriately rescaled vertical trace. -/
theorem mellinInv_exp_eq_fourier (F : ℂ → ℂ) (σ x : ℝ) :
    mellinInv σ F (Real.exp x) =
      logWeight (-σ) x * 𝓕 (fun y : ℝ ↦ verticalTrace F σ (2 * Real.pi * y)) x := by
  rw [mellinInv_eq_fourierInv _ _ (Real.exp_pos x), Real.log_exp, Real.fourierInv_eq_fourier_neg,
    neg_neg, smul_eq_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    mul_comm (x : ℂ) (-(σ : ℂ))]

theorem main
    (a : ℝ) (b : WithTop ℝ) (hab : (a : WithTop ℝ) < b) (N : ℝ) (hN : 2 < N) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | a < s.re ∧ (s.re : WithTop ℝ) < b})
    (hBound : ∀ c d : ℝ, a < c → c ≤ d → (d : WithTop ℝ) < b →
      ∃ C : ℝ, ∀ s : ℂ, c ≤ s.re → s.re ≤ d → ‖s‖ ^ N * ‖F s‖ ≤ C)
    (m : ℕ) (hm : (m : ℝ) < N - 1) :
    ∃ φ : ℝ → ℂ, ContDiffOn ℝ m φ (Set.Ioi 0) ∧
      (∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b →
        ContDiff ℝ m (fun x : ℝ => (Real.exp (σ * x) : ℂ) * φ (Real.exp x)) ∧
        (∀ j : ℕ, j ≤ m → Tendsto
          (iteratedDeriv j (fun x : ℝ => (Real.exp (σ * x) : ℂ) * φ (Real.exp x)))
          (cocompact ℝ) (𝓝 0)) ∧
        MemLp (fun x : ℝ => (Real.exp (σ * x) : ℂ) * φ (Real.exp x)) 2 volume) ∧
      ∀ s : ℂ, a < s.re → (s.re : WithTop ℝ) < b → MellinConvergent φ s ∧ mellin φ s = F s := by
  let trace (σ : ℝ) := fun y : ℝ ↦ verticalTrace F σ (2 * Real.pi * y)
  let g (σ : ℝ) : ℝ → ℂ := 𝓕 (trace σ)
  have between {σ : ℝ} (hσ : (σ : WithTop ℝ) < b) :
      ∃ d : ℝ, σ < d ∧ (d : WithTop ℝ) < b := by
    obtain ⟨d, hd₁, hd₂⟩ := exists_between hσ
    lift d to ℝ using ne_of_lt (hd₂.trans_le le_top)
    exact ⟨d, WithTop.coe_lt_coe.mp hd₁, hd₂⟩
  have hsub (c d : ℝ) (hca : a < c) (hdb : (d : WithTop ℝ) < b) :
      Complex.re ⁻¹' Icc c d ⊆ {s : ℂ | a < s.re ∧ (s.re : WithTop ℝ) < b} := by
    intro z hz
    exact ⟨hca.trans_le hz.1, (WithTop.coe_le_coe.mpr hz.2).trans_lt hdb⟩
  have hdecayStrip (c d : ℝ) (hca : a < c) (hcd : c ≤ d) (hdb : (d : WithTop ℝ) < b) :
      ∃ C ≥ (0 : ℝ), ∀ σ ∈ Icc c d, ∀ y : ℝ,
        ‖verticalTrace F σ y‖ ≤ C * (1 + ‖y‖) ^ (-N) := by
    obtain ⟨C₀, hC₀⟩ := hBound c d hca hcd hdb
    exact verticalTrace_polynomialDecay (by linarith)
      (hF.continuousOn.mono (hsub c d hca hdb)) hC₀
  obtain ⟨σ₀, hσ₀a, hσ₀b⟩ := between hab
  have hcont (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      Continuous (verticalTrace F σ) :=
    hF.continuousOn.comp_continuous (by fun_prop) fun y ↦ by simpa using And.intro hσa hσb
  have hverticalMoment (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b)
      (j : ℕ) (hj : (j : ℝ) < N - 1) :
      Integrable (fun y : ℝ ↦ y ^ j • verticalTrace F σ y) := by
    obtain ⟨C, _, hdecay⟩ := hdecayStrip σ σ hσa le_rfl hσb
    exact integrable_verticalTrace_moment (hcont σ hσa hσb) (hdecay σ ⟨le_rfl, le_rfl⟩) j hj
  have hline (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      Complex.VerticalIntegrable F σ := by
    simpa [Complex.VerticalIntegrable] using hverticalMoment σ hσa hσb 0 (by simp; linarith)
  have hmoment (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) (j : ℕ) (hj : j ≤ m) :
      Integrable (fun y : ℝ ↦ y ^ j • trace σ y) := by
    have hscale : 2 * Real.pi ≠ 0 := by positivity
    have hi := hverticalMoment σ hσa hσb j ((Nat.cast_le.mpr hj).trans_lt hm)
    convert (hi.comp_mul_left' hscale).smul ((2 * Real.pi)⁻¹ ^ j) using 1
    funext y
    simp only [trace, Pi.smul_apply, smul_smul, ← mul_pow, ← mul_assoc,
      inv_mul_cancel₀ hscale, one_mul]
  have hsmooth (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      ContDiff ℝ (m : ℕ∞) (g σ) ∧
        ∀ j ≤ m, Tendsto (iteratedDeriv j (g σ)) (cocompact ℝ) (𝓝 0) := by
    have hmom (j : ℕ) (hj : (j : ℕ∞) ≤ m) := hmoment σ hσa hσb j (by exact_mod_cast hj)
    refine ⟨Real.contDiff_fourier (fun j hj ↦ ?_), fun j hj ↦ ?_⟩
    · simpa only [norm_smul, norm_pow] using (hmom j hj).norm
    · change Tendsto (iteratedDeriv j (𝓕 (trace σ))) _ _
      rw [Real.iteratedDeriv_fourier (N := (m : ℕ∞)) hmom (by exact_mod_cast hj)]
      exact Real.zero_at_infty_fourier _
  have hordered (c d : ℝ) (hca : a < c) (hcd : c ≤ d) (hdb : (d : WithTop ℝ) < b)
      {t : ℝ} (ht : 0 < t) : mellinInv c F t = mellinInv d F t := by
    have hcb : (c : WithTop ℝ) < b := (WithTop.coe_le_coe.mpr hcd).trans_lt hdb
    obtain ⟨C, hC, hdecay⟩ := hdecayStrip c d hca hcd hdb
    exact mellinInv_eq_of_verticalTrace_decay hcd (hF.mono (hsub c d hca hdb))
      (hline c hca hcb) (hline d (hca.trans_le hcd) hdb) hC (by linarith) hdecay ht
  let p (x : ℝ) := logWeight (-σ₀) x * g σ₀ x
  have hp : ContDiff ℝ (m : ℕ∞) p := by
    have hw : ContDiff ℝ (m : ℕ∞) (logWeight (-σ₀)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ (m : ℕ∞)
        (fun x : ℝ ↦ Real.exp (-σ₀ * x)))
    exact hw.mul (hsmooth σ₀ hσ₀a hσ₀b).1
  have hweight (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      (fun x ↦ logWeight σ x * p x) = g σ := by
    funext x
    have hshift : mellinInv σ₀ F (Real.exp x) = mellinInv σ F (Real.exp x) := by
      rcases le_total σ₀ σ with h | h
      · exact hordered σ₀ σ hσ₀a h hσb (Real.exp_pos x)
      · exact (hordered σ σ₀ hσa h hσ₀b (Real.exp_pos x)).symm
    rw [mellinInv_exp_eq_fourier, mellinInv_exp_eq_fourier] at hshift
    change logWeight σ x * p x = g σ x
    rw [show p x = logWeight (-σ) x * g σ x from hshift, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    simp
  have htransition (σ τ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b)
      (hτa : a < τ) (hτb : (τ : WithTop ℝ) < b) (x : ℝ) :
      g σ x = logWeight (σ - τ) x * g τ x := by
    have he : logWeight σ x = logWeight (σ - τ) x * logWeight τ x := by
      change (Real.exp (σ * x) : ℂ) = (Real.exp ((σ - τ) * x) : ℂ) * (Real.exp (τ * x) : ℂ)
      rw [← Complex.ofReal_mul, ← Real.exp_add, sub_mul, sub_add_cancel]
    calc
      g σ x = logWeight σ x * p x := (congrFun (hweight σ hσa hσb) x).symm
      _ = (logWeight (σ - τ) x * logWeight τ x) * p x := congrArg (· * p x) he
      _ = logWeight (σ - τ) x * (logWeight τ x * p x) := mul_assoc _ _ _
      _ = _ := congrArg (logWeight (σ - τ) x * ·) (congrFun (hweight τ hτa hτb) x)
  let K (σ : ℝ) := ∫ y, ‖trace σ y‖
  have hK (σ : ℝ) (x : ℝ) : ‖g σ x‖ ≤ K σ := by
    change ‖𝓕 (trace σ) x‖ ≤ K σ
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext v
    simp
  have hgInt (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) : Integrable (g σ) := by
    obtain ⟨c, hca, hcσ⟩ := exists_between hσa
    obtain ⟨d, hσd, hdb⟩ := between hσb
    have hcb : (c : WithTop ℝ) < b := (WithTop.coe_lt_coe.mpr hcσ).trans hσb
    have hda := hσa.trans hσd
    have hmeas : AEStronglyMeasurable (g σ) volume :=
      (hsmooth σ hσa hσb).1.continuous.aestronglyMeasurable
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · apply ((integrableOn_exp_mul_Iic (sub_pos.mpr hcσ) 0).const_mul (K c)).mono'
        hmeas.restrict
      filter_upwards with x
      rw [htransition σ c hσa hσb hca hcb x, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      exact mul_le_mul_of_nonneg_right (hK c x) (Real.exp_pos _).le
    · apply ((integrableOn_exp_mul_Ioi (sub_neg.mpr hσd) 0).const_mul (K d)).mono'
        hmeas.restrict
      filter_upwards with x
      rw [htransition σ d hσa hσb hda hdb x, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      exact mul_le_mul_of_nonneg_right (hK d x) (Real.exp_pos _).le
  refine ⟨fun t ↦ p (Real.log t),
    hp.contDiffOn.comp (Real.contDiffOn_log.mono ?_) (mapsTo_univ _ _), ?_, ?_⟩
  · intro x hx
    exact ne_of_gt hx
  · intro σ hσa hσb
    simp only [Real.log_exp, hweight σ hσa hσb]
    obtain ⟨h1, h2⟩ := hsmooth σ hσa hσb
    refine ⟨h1, h2, ?_⟩
    apply (integrable_norm_rpow_iff (hgInt σ hσa hσb).aestronglyMeasurable
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)).mp
    apply ((hgInt σ hσa hσb).norm.const_mul (K σ)).mono' (by
      simp only [ENNReal.toReal_ofNat]
      exact ((hsmooth σ hσa hσb).1.continuous.norm.rpow_const
        (fun _ ↦ Or.inr (by norm_num))).aestronglyMeasurable)
    filter_upwards with x
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _)]
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hK σ x) (norm_nonneg _)
  · intro s hs1 hs2
    have hi := hgInt s.re hs1 hs2
    refine ⟨mellinConvergent_of_integrable_logWeight p s (by rwa [hweight s.re hs1 hs2]), ?_⟩
    rw [mellin_eq_fourier]
    have hEq : (fun u : ℝ ↦ Real.exp (-s.re * u) • p (Real.log (Real.exp (-u)))) =
        𝓕⁻ (trace s.re) := by
      funext u
      rw [Real.log_exp, Complex.real_smul, neg_mul, ← mul_neg, Real.fourierInv_eq_fourier_neg]
      exact congrFun (hweight s.re hs1 hs2) (-u)
    have hct : Continuous (trace s.re) := (hcont s.re hs1 hs2).comp (by fun_prop)
    have hit : Integrable (trace s.re) := by simpa using hmoment s.re hs1 hs2 0 (Nat.zero_le m)
    rw [hEq, hct.fourier_fourierInv_eq hit hi]
    change F (verticalPoint s.re (2 * Real.pi * (s.im / (2 * Real.pi)))) = F s
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (show 2 * Real.pi ≠ 0 by positivity)]
    exact congrArg F (Complex.re_add_im s)

end Sol_MellinAsymptotics_exists_mellin_eq_of_polynomial_decay

theorem solution
    (a : ℝ) (b : WithTop ℝ) (hab : (a : WithTop ℝ) < b) (N : ℝ) (hN : 2 < N) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {s : ℂ | a < s.re ∧ (s.re : WithTop ℝ) < b})
    (hbd : ∀ c d : ℝ, a < c → c ≤ d → (d : WithTop ℝ) < b →
      ∃ C : ℝ, ∀ s : ℂ, c ≤ s.re → s.re ≤ d → ‖s‖ ^ N * ‖f s‖ ≤ C)
    (m : ℕ) (hm : (m : ℝ) < N - 1) :
    ∃ φ : ℝ → ℂ, ContDiffOn ℝ m φ (Set.Ioi 0) ∧
      (∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b →
        ContDiff ℝ m (fun x : ℝ => (Real.exp (σ * x) : ℂ) * φ (Real.exp x)) ∧
        (∀ j : ℕ, j ≤ m → Tendsto
          (iteratedDeriv j (fun x : ℝ => (Real.exp (σ * x) : ℂ) * φ (Real.exp x)))
          (cocompact ℝ) (𝓝 0)) ∧
        MemLp (fun x : ℝ => (Real.exp (σ * x) : ℂ) * φ (Real.exp x)) 2 volume) ∧
      ∀ s : ℂ, a < s.re → (s.re : WithTop ℝ) < b → MellinConvergent φ s ∧ mellin φ s = f s :=
  Sol_MellinAsymptotics_exists_mellin_eq_of_polynomial_decay.main a b hab N hN f hf hbd m hm
