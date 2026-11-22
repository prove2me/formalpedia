-- Prove2me | solution 1 for MasulloRH.rapid_packet_translate_orthogonality_with_L2_differences
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T20:06:00.17618+00:00
-- url     : https://prove2.me/submissions/6dbfbd2b-6aef-487e-b29d-ada44feabe73

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace Convolution

namespace RapidPacketAux

/-- The `L²` Fourier transform of an `L¹ ∩ L²` function is given a.e. by the Fourier integral. -/
lemma l2_fourier_ae (g : ℝ → ℂ) (h1 : Integrable g) (h2 : MemLp g 2) :
    ((𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 g := by
  have hc : Continuous (𝓕 g) := by
    have := VectorFourier.fourierIntegral_continuous (V := ℝ) (W := ℝ) (μ := volume)
      (L := innerₗ ℝ) (f := g) Real.continuous_fourierChar continuous_inner h1
    exact this
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num)) hc.locallyIntegrable ?_
  intro h hh hsupp
  set ψ : 𝓢(ℝ, ℂ) := (hsupp.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hh) with hψ
  have hψx : ∀ x, ψ x = (h x : ℂ) := fun x => rfl
  have e1 : ∫ x, h x • ((𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
      = Lp.toTemperedDistribution (𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) ψ := by
    rw [Lp.toTemperedDistribution_apply]
    simp [hψx]
  rw [e1, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply]
  have e2 : ∫ x, (𝓕 ψ) x • (h2.toLp g : ℝ → ℂ) x = ∫ x, (𝓕 (ψ : ℝ → ℂ)) x • g x := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx, SchwartzMap.fourier_coe]
  rw [e2]
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (L := innerₗ ℝ) (f := (ψ : ℝ → ℂ)) (g := g)
    Real.continuous_fourierChar continuous_inner ψ.integrable h1
  have e3 : ∫ x, h x • 𝓕 g x = ∫ x, ψ x • 𝓕 g x := by simp [hψx]
  rw [e3]
  have e4 : ∀ x, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ).flip g x = 𝓕 g x := by
    intro x
    rw [Real.fourier_eq]
    simp [VectorFourier.fourierIntegral]
  simp only [e4] at this
  exact this


/-- The Fourier--Laplace transform of a function with all exponential moments is entire. -/
lemma entire_fourier (u : ℝ → ℂ) (hu : Continuous u)
    (hdec : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * |x|) * ‖u x‖)) :
    Differentiable ℂ (fun z : ℂ => ∫ v : ℝ, Complex.exp (((-2 * Real.pi * v : ℝ) : ℂ) * z * Complex.I) * u v) := by
  intro z₀
  have hnorm : ∀ (z : ℂ) (v : ℝ), ‖Complex.exp (((-2 * Real.pi * v : ℝ) : ℂ) * z * Complex.I)‖
      ≤ Real.exp (2 * Real.pi * ‖z‖ * |v|) := by
    intro z v
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    have : (((-2 * Real.pi * v : ℝ) : ℂ) * z * Complex.I).re = 2 * Real.pi * v * z.im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this]
    have h1 : v * z.im ≤ |v| * ‖z‖ := by
      calc v * z.im ≤ |v * z.im| := le_abs_self _
        _ = |v| * |z.im| := abs_mul _ _
        _ ≤ |v| * ‖z‖ := by gcongr; exact Complex.abs_im_le_norm z
    have hpi := Real.pi_pos
    nlinarith
  have hcont : ∀ z : ℂ, Continuous
      (fun v : ℝ => Complex.exp (((-2 * Real.pi * v : ℝ) : ℂ) * z * Complex.I) * u v) := by
    intro z; fun_prop
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
    (F := fun (z : ℂ) (v : ℝ) => Complex.exp (((-2 * Real.pi * v : ℝ) : ℂ) * z * Complex.I) * u v)
    (F' := fun (z : ℂ) (v : ℝ) => (((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-2 * Real.pi * v : ℝ) : ℂ) * z * Complex.I) * u v)
    (x₀ := z₀) (s := Metric.ball z₀ 1)
    (bound := fun v => Real.exp ((2 * Real.pi * (‖z₀‖ + 2)) * |v|) * ‖u v‖)
    (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable)
    ?_ ?_ ?_ (hdec _) ?_
  · exact hmain.2.differentiableAt
  · refine (hdec (2 * Real.pi * ‖z₀‖)).mono' (hcont z₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_mul]
    gcongr
    exact hnorm z₀ v
  · exact (by fun_prop : Continuous _).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v z hz => ?_
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by ring_nf
        _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
        _ ≤ ‖z₀‖ + 1 := by linarith
    rw [norm_mul, norm_mul]
    gcongr
    have h1 : ‖((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I‖ ≤ Real.exp (2 * Real.pi * |v|) := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have : |-2 * Real.pi * v| = 2 * Real.pi * |v| := by
        rw [abs_mul, abs_mul]; simp [abs_of_pos Real.pi_pos]
      rw [this]
      linarith [Real.add_one_le_exp (2 * Real.pi * |v|)]
    have h2 := hnorm z v
    have h3 : Real.exp (2 * Real.pi * ‖z‖ * |v|) ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1) * |v|) := by
      apply Real.exp_le_exp.2
      have := Real.pi_pos
      have := abs_nonneg v
      gcongr
    calc _ ≤ Real.exp (2 * Real.pi * |v|) * Real.exp (2 * Real.pi * (‖z₀‖ + 1) * |v|) := by
          gcongr
          exact h2.trans h3
      _ = _ := by rw [← Real.exp_add]; ring_nf
  · refine Filter.Eventually.of_forall fun v z _ => ?_
    have : HasDerivAt (fun z : ℂ => ((-2 * Real.pi * v : ℝ) : ℂ) * z * Complex.I)
        (((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I) z := by
      simpa using ((hasDerivAt_id z).const_mul ((-2 * Real.pi * v : ℝ) : ℂ)).mul_const Complex.I
    simpa [mul_comm, mul_assoc, mul_left_comm] using (this.cexp.mul_const (u v))

lemma fourier_ne_zero_ae (u : ℝ → ℂ) (hu : Continuous u) (hu0 : u ≠ 0)
    (hdec : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * |x|) * ‖u x‖)) :
    ∀ᵐ ξ : ℝ, 𝓕 u ξ ≠ 0 := by
  have hint : Integrable u := by
    have := hdec 0
    simp only [zero_mul, Real.exp_zero, one_mul] at this
    exact (integrable_norm_iff hu.aestronglyMeasurable).1 this
  set F : ℂ → ℂ := fun z : ℂ =>
    ∫ v : ℝ, Complex.exp (((-2 * Real.pi * v : ℝ) : ℂ) * z * Complex.I) * u v with hF
  have hFd : Differentiable ℂ F := entire_fourier u hu hdec
  have hFu : ∀ ξ : ℝ, 𝓕 u ξ = F ξ := by
    intro ξ
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp [hF]
  have han : AnalyticOnNhd ℝ (fun ξ : ℝ => F ξ) Set.univ := by
    intro ξ _
    have h1 : AnalyticAt ℝ F (ξ : ℂ) := (hFd.analyticAt _).restrictScalars
    exact h1.comp (Complex.ofRealCLM.analyticAt ξ)
  by_cases hex : ∃ ξ : ℝ, F ξ ≠ 0
  · obtain ⟨ξ₀, hξ₀⟩ := hex
    have hcod := han.preimage_zero_mem_codiscrete hξ₀
    have hcount : ((fun ξ : ℝ => F ξ) ⁻¹' {0}).Countable := by
      have := (HereditarilyLindelofSpace.isLindelof ((fun ξ : ℝ => F ξ) ⁻¹' {0} ∩ Set.univ)).countable_of_isDiscrete
        (isDiscrete_of_codiscreteWithin (by rw [Set.preimage_compl] at hcod; exact hcod))
      simpa using this
    have hnull := hcount.measure_zero (volume : Measure ℝ)
    rw [ae_iff]
    convert hnull using 2
    ext ξ
    simp [hFu]
  · exfalso
    push Not at hex
    have h0 : 𝓕 u = 0 := by
      ext ξ; rw [hFu, hex]; rfl
    have := hu.fourierInv_fourier_eq hint (by rw [h0]; exact integrable_zero _ _ _)
    apply hu0
    rw [← this, h0]
    ext x
    simp [Real.fourierInv_eq]


lemma fourier_cont (g : ℝ → ℂ) (h1 : Integrable g) : Continuous (𝓕 g) := by
  have := VectorFourier.fourierIntegral_continuous (V := ℝ) (W := ℝ) (μ := volume)
    (L := innerₗ ℝ) (f := g) Real.continuous_fourierChar continuous_inner h1
  exact this

lemma key (β u : ℝ → ℂ) (hβ : Continuous β) (M : ℝ) (hM : ∀ x, ‖β x‖ ≤ M) (hβ2 : MemLp β 2)
    (hint : Integrable u) (hW : ∀ᵐ ξ : ℝ, 𝓕 u ξ ≠ 0)
    (h : ∀ c : ℝ, ∫ x, β x * (starRingEnd ℂ) (u (x - c)) = 0) : ∀ x, β x = 0 := by
  set Bt : Lp ℂ 2 (volume : Measure ℝ) := hβ2.toLp β with hBt
  set B : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 Bt with hB
  have hprod : ∀ᵐ ξ : ℝ, (starRingEnd ℂ) (𝓕 u ξ) * B ξ = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · have h1 : LocallyIntegrable (B : ℝ → ℂ) volume :=
        (Lp.memLp B).locallyIntegrable (by norm_num)
      rw [← locallyIntegrableOn_univ] at h1 ⊢
      exact h1.continuousOn_mul
        ((Complex.continuous_conj.comp (fourier_cont u hint)).continuousOn) isOpen_univ.isLocallyClosed
    · intro k hk hsupp
      set ψ : 𝓢(ℝ, ℂ) :=
        (hsupp.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp hk) with hψ
      have hψx : ∀ x, ψ x = (k x : ℂ) := fun x => rfl
      set φ : 𝓢(ℝ, ℂ) := 𝓕⁻ ψ with hφ
      have hφψ : 𝓕 φ = ψ := by rw [hφ]; exact FourierTransform.fourier_fourierInv_eq ψ
      set g : ℝ → ℂ := (φ : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] u with hg
      have hg1 : Integrable g := φ.integrable.integrable_convolution _ hint
      have hgF : ∀ ξ, 𝓕 g ξ = k ξ * 𝓕 u ξ := by
        intro ξ
        rw [hg, Real.fourier_mul_convolution_eq φ.integrable hint ξ, ← SchwartzMap.fourier_coe,
          hφψ, hψx]
      have hgx : ∀ x, g x = ∫ t, φ t * u (x - t) := fun x => rfl
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
        refine ⟨‖φ.toBoundedContinuousFunction‖ * ∫ t, ‖u t‖, fun x => ?_⟩
        rw [hgx]
        calc ‖∫ t, φ t * u (x - t)‖ ≤ ∫ t, ‖φ t * u (x - t)‖ := norm_integral_le_integral_norm _
          _ ≤ ∫ t, ‖φ.toBoundedContinuousFunction‖ * ‖u (x - t)‖ := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
              ((hint.comp_sub_left x).norm.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
            simp only [norm_mul]
            gcongr
            exact φ.toBoundedContinuousFunction.norm_coe_le_norm t
          _ = _ := by
            rw [integral_const_mul, integral_sub_left_eq_self (fun t => ‖u t‖)]
      have hg2 : MemLp g 2 := by
        rw [memLp_two_iff_integrable_sq_norm hg1.aestronglyMeasurable]
        refine (hg1.norm.const_mul C).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
        exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
      set G : Lp ℂ 2 (volume : Measure ℝ) := hg2.toLp g with hG
      have hpl : ⟪𝓕 G, B⟫ = ⟪G, Bt⟫ := Lp.inner_fourier_eq G Bt
      have hR : ⟪G, Bt⟫ = 0 := by
        rw [L2.inner_def]
        have e1 : ∫ a, ⟪G a, Bt a⟫ = ∫ x, (starRingEnd ℂ) (g x) * β x := by
          apply integral_congr_ae
          filter_upwards [hg2.coeFn_toLp, hβ2.coeFn_toLp] with x h1 h2
          rw [h1, h2, RCLike.inner_apply']
        rw [e1]
        have e2 : ∀ x, (starRingEnd ℂ) (g x) * β x
            = ∫ t, (starRingEnd ℂ) (φ t) * (starRingEnd ℂ) (u (x - t)) * β x := by
          intro x
          rw [hgx, ← integral_conj, ← integral_mul_const]
          simp [map_mul]
        simp_rw [e2]
        rw [integral_integral_swap]
        · have e3 : ∀ t, ∫ x, (starRingEnd ℂ) (φ t) * (starRingEnd ℂ) (u (x - t)) * β x = 0 := by
            intro t
            have e4 : ∫ x, (starRingEnd ℂ) (φ t) * (starRingEnd ℂ) (u (x - t)) * β x
                = (starRingEnd ℂ) (φ t) * ∫ x, β x * (starRingEnd ℂ) (u (x - t)) := by
              rw [← integral_const_mul]
              congr 1
              ext x
              ring
            rw [e4, h t, mul_zero]
          simp [e3]
        · have h0 := φ.integrable.convolution_integrand (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
            (ContinuousLinearMap.mul ℂ ℂ) hint
          have h1 : Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (φ p.2 * u (p.1 - p.2)))
              (volume.prod volume) :=
            h0.mono (Complex.continuous_conj.comp_aestronglyMeasurable h0.aestronglyMeasurable)
              (Filter.Eventually.of_forall fun p => by simp)
          have h2 := h1.mul_bdd (c := M) (g := fun p : ℝ × ℝ => β p.1)
            (hβ.comp continuous_fst).aestronglyMeasurable
            (Filter.Eventually.of_forall fun p => hM p.1)
          convert h2 using 1
          ext p
          simp [Function.uncurry, map_mul]
      have hL : ⟪𝓕 G, B⟫ = ∫ x, k x • ((starRingEnd ℂ) (𝓕 u x) * B x) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [l2_fourier_ae g hg1 hg2] with x hx
        rw [hx, hgF]
        simp [mul_comm, mul_left_comm]
      rw [← hL, hpl, hR]
  have hB0 : B = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.2
    filter_upwards [hW, hprod] with ξ h1 h2
    simpa [h1] using h2
  have hBt0 : Bt = 0 := by
    have : ‖Bt‖ = 0 := by rw [← Lp.norm_fourier_eq Bt, ← hB, hB0, norm_zero]
    exact norm_eq_zero.1 this
  have hae : β =ᵐ[volume] 0 := by
    have h1 := hβ2.coeFn_toLp
    have h2 := Lp.eq_zero_iff_ae_eq_zero.1 hBt0
    exact h1.symm.trans h2
  intro x
  have := (Continuous.ae_eq_iff_eq volume hβ continuous_zero).1 hae
  rw [this]; rfl

end RapidPacketAux

theorem solution (b u : ℝ → ℂ) (hb : Continuous b) (hbd : ∃ M : ℝ, ∀ x : ℝ, ‖b x‖ ≤ M) (hd : ∀ d : ℝ, MemLp (fun x => b (x+d) - b x) 2 volume) (hu : Continuous u) (hu0 : u ≠ 0) (hdec : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * |x|) * ‖u x‖)) (hpair : ∀ c : ℝ, (∫ x : ℝ, b x * (starRingEnd ℂ) (u (x-c))) = 0) : ∃ m : ℂ, ∀ x : ℝ, b x = m := by
  obtain ⟨M, hM⟩ := hbd
  have hint : Integrable u := by
    have := hdec 0
    simp only [zero_mul, Real.exp_zero, one_mul] at this
    exact (integrable_norm_iff hu.aestronglyMeasurable).1 this
  have hW := RapidPacketAux.fourier_ne_zero_ae u hu hu0 hdec
  have hconj : ∀ c : ℝ, Integrable (fun x : ℝ => (starRingEnd ℂ) (u (x - c))) := by
    intro c
    have h0 := hint.comp_sub_right c
    exact h0.mono (Complex.continuous_conj.comp_aestronglyMeasurable h0.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => by simp)
  have hzero : ∀ d x : ℝ, b (x + d) - b x = 0 := by
    intro d
    refine RapidPacketAux.key (fun x => b (x + d) - b x) u (by fun_prop) (M + M) ?_ (hd d) hint hW ?_
    · intro x
      exact (norm_sub_le _ _).trans (add_le_add (hM _) (hM _))
    · intro c
      have i1 : Integrable (fun x : ℝ => b (x + d) * (starRingEnd ℂ) (u (x - c))) :=
        (hconj c).bdd_mul (c := M) (by fun_prop : Continuous fun x : ℝ => b (x + d)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => hM _)
      have i2 : Integrable (fun x : ℝ => b x * (starRingEnd ℂ) (u (x - c))) :=
        (hconj c).bdd_mul (c := M) hb.aestronglyMeasurable (Filter.Eventually.of_forall fun x => hM _)
      have e1 : ∫ x : ℝ, b (x + d) * (starRingEnd ℂ) (u (x - c)) = 0 := by
        have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
          (fun y : ℝ => b y * (starRingEnd ℂ) (u (y - (c + d)))) d
        rw [hpair] at this
        rw [← this]
        congr 1
        ext x
        congr 3
        ring
      simp only [sub_mul]
      rw [integral_sub i1 i2, e1, hpair, sub_zero]
  refine ⟨b 0, fun x => ?_⟩
  have := hzero x 0
  rw [zero_add] at this
  exact sub_eq_zero.1 this

