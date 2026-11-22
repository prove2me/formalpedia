-- Prove2me | solution 1 for MasulloGRH.paley_wiener_compact_support
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T20:08:38.190945+00:00
-- url     : https://prove2.me/submissions/6dd23f51-d609-4bb0-8662-6a11f40c5372

import Mathlib
import Definitions.Def_MasulloGRH_SchauderBases
set_option autoImplicit false
open MeasureTheory Complex Real Set Filter Topology FourierTransform SchwartzMap
open scoped ContDiff

namespace MasulloGRHPaleyWienerAux


/-- self-adjointness of the Fourier integral for L¹ functions on ℝ. -/
theorem fourier_flip {G ψ : ℝ → ℂ} (hG : Integrable G) (hψ : Integrable ψ) :
    ∫ x, 𝓕 ψ x • G x = ∫ x, ψ x • 𝓕 G x := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (L := innerₗ ℝ) (f := ψ) (g := G)
    Real.continuous_fourierChar continuous_inner hψ hG
  simpa using! this

theorem fourier_continuous {G : ℝ → ℂ} (hG : Integrable G) : Continuous (𝓕 G) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hG

theorem fourier_L1L2 {G : ℝ → ℂ} (hG1 : Integrable G) (hG2 : MemLp G 2) :
    ((𝓕 (hG2.toLp G) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 G := by
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  · exact (fourier_continuous hG1).locallyIntegrable
  intro ρ hρ hρc
  have hc : HasCompactSupport (fun x => (ρ x : ℂ)) := hρc.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hd : ContDiff ℝ ∞ (fun x => (ρ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hρ
  set ψ : 𝓢(ℝ, ℂ) := hc.toSchwartzMap hd with hψ
  have h1 : ∫ x, ρ x • ((𝓕 (hG2.toLp G) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
      = Lp.toTemperedDistribution (𝓕 (hG2.toLp G) : Lp ℂ 2 (volume : Measure ℝ)) ψ := by
    rw [Lp.toTemperedDistribution_apply]
    rfl
  rw [h1, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply]
  have h2 : ∫ x, (𝓕 ψ) x • (hG2.toLp G : ℝ → ℂ) x = ∫ x, (𝓕 ψ) x • G x := by
    apply integral_congr_ae
    filter_upwards [hG2.coeFn_toLp] with x hx
    rw [hx]
  rw [h2, SchwartzMap.fourier_coe, fourier_flip hG1 ψ.integrable]
  rfl



theorem norm_mul_exp_le {F : ℝ → ℂ} {B : ℝ} (hB : ∀ t, B < |t| → F t = 0) (c w : ℂ) (t : ℝ) :
    ‖F t * cexp (c * t * w)‖ ≤ ‖F t‖ * rexp (‖c‖ * |B| * ‖w‖) := by
  by_cases ht : B < |t|
  · rw [hB t ht]; simp
  · replace ht := not_lt.mp ht
    rw [norm_mul, Complex.norm_exp]
    gcongr
    calc (c * t * w).re ≤ ‖c * t * w‖ := Complex.re_le_norm _
      _ = ‖c‖ * |t| * ‖w‖ := by simp
      _ ≤ ‖c‖ * |B| * ‖w‖ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (ht.trans (le_abs_self B)) (norm_nonneg c)) (norm_nonneg w)

theorem integrable_mul_exp {F : ℝ → ℂ} (hF : Integrable F) {B : ℝ}
    (hB : ∀ t, B < |t| → F t = 0) (c w : ℂ) :
    Integrable (fun t : ℝ => F t * cexp (c * t * w)) := by
  refine Integrable.mono' (hF.norm.mul_const (rexp (‖c‖ * |B| * ‖w‖))) ?_ ?_
  · exact hF.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ => cexp (c * t * w)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => norm_mul_exp_le hB c w t

theorem hasDerivAt_expInt {F : ℝ → ℂ} (hF : Integrable F) {B : ℝ}
    (hB : ∀ t, B < |t| → F t = 0) (c z : ℂ) :
    HasDerivAt (fun z : ℂ => ∫ t : ℝ, F t * cexp (c * t * z))
      (∫ t : ℝ, F t * (c * t) * cexp (c * t * z)) z := by
  have hF2 : Integrable (fun t : ℝ => F t * (c * t)) := by
    refine Integrable.mono' (hF.norm.mul_const (‖c‖ * |B|)) ?_ ?_
    · exact hF.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ => c * (t : ℂ)).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      by_cases ht : B < |t|
      · rw [hB t ht]; simp
      · replace ht := not_lt.mp ht
        rw [norm_mul]
        gcongr
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (ht.trans (le_abs_self B)) (norm_nonneg c)
  have hB2 : ∀ t, B < |t| → F t * (c * t) = 0 := fun t ht => by rw [hB t ht, zero_mul]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := Metric.ball z 1)
    (F := fun (w : ℂ) (t : ℝ) => F t * cexp (c * t * w))
    (F' := fun (w : ℂ) (t : ℝ) => F t * (c * t) * cexp (c * t * w))
    (bound := fun t => ‖F t * (c * t)‖ * rexp (‖c‖ * |B| * (‖z‖ + 1)))
    (Metric.ball_mem_nhds z one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun w => (integrable_mul_exp hF hB c w).aestronglyMeasurable
  · exact integrable_mul_exp hF hB c z
  · exact (integrable_mul_exp hF2 hB2 c z).aestronglyMeasurable
  · refine Eventually.of_forall fun t w hw => ?_
    refine (norm_mul_exp_le hB2 c w t).trans ?_
    gcongr
    have : ‖w - z‖ < 1 := by simpa [dist_eq_norm] using hw
    calc ‖w‖ = ‖z + (w - z)‖ := by rw [add_sub_cancel]
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 1 := by linarith
  · exact hF2.norm.mul_const _
  · refine Eventually.of_forall fun t w _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => c * t * w) (c * t) w := by
      simpa using (hasDerivAt_id w).const_mul (c * (t : ℂ))
    have h2 : HasDerivAt (fun w : ℂ => F t * cexp (c * t * w))
        (F t * (cexp (c * t * w) * (c * t))) w := (h1.cexp).const_mul (F t)
    exact h2.congr_deriv (by ring)


/-- Fourier–Laplace transform with Mathlib's normalisation. -/
noncomputable def FL (φ : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t : ℝ, φ t * cexp (-(2 * π * I) * t * z)

/-- Test functions: smooth, compactly supported, vanishing to the left of `a`. -/
def TestFn (a : ℝ) (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ ∀ t, t < a → φ t = 0

theorem TestFn.integrable {a : ℝ} {φ : ℝ → ℂ} (h : TestFn a φ) : Integrable φ :=
  h.1.continuous.integrable_of_hasCompactSupport h.2.1

theorem TestFn.bdd {a : ℝ} {φ : ℝ → ℂ} (h : TestFn a φ) : ∃ B : ℝ, ∀ t, B < |t| → φ t = 0 := by
  obtain ⟨B, hB⟩ := h.2.1.isCompact.isBounded.exists_norm_le
  refine ⟨B, fun t ht => ?_⟩
  by_contra hne
  have := hB t (subset_tsupport _ hne)
  rw [Real.norm_eq_abs] at this
  linarith

theorem TestFn.deriv {a : ℝ} {φ : ℝ → ℂ} (h : TestFn a φ) : TestFn a (deriv φ) := by
  refine ⟨(contDiff_infty_iff_deriv.mp h.1).2, h.2.1.deriv, fun t ht => ?_⟩
  by_contra hne
  have h1 : t ∈ tsupport φ := support_deriv_subset hne
  have h2 : tsupport φ ⊆ Ici a := by
    apply closure_minimal _ isClosed_Ici
    intro s hs
    by_contra hsa
    exact hs (h.2.2 s (not_le.mp hsa))
  exact absurd (h2 h1) (not_le.mpr ht)

theorem TestFn.mul_lin {a : ℝ} {φ : ℝ → ℂ} (h : TestFn a φ) (c : ℂ) :
    TestFn a (fun t => φ t * (c * t)) := by
  refine ⟨h.1.mul (contDiff_const.mul Complex.ofRealCLM.contDiff), ?_, fun t ht => ?_⟩
  · exact h.2.1.mul_right
  · simp [h.2.2 t ht]

theorem FL_norm_le {a : ℝ} {φ : ℝ → ℂ} (h : TestFn a φ) {z : ℂ} (hz : z.im ≤ 0) :
    ‖FL φ z‖ ≤ (∫ t, ‖φ t‖) * rexp (2 * π * a * z.im) := by
  rw [FL, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (h.integrable.norm.mul_const _) (Eventually.of_forall fun t => ?_)
  by_cases ht : t < a
  · simp [h.2.2 t ht]
  · replace ht := not_lt.mp ht
    rw [norm_mul, Complex.norm_exp]
    gcongr
    have : (-(2 * π * I) * t * z).re = 2 * π * t * z.im := by simp
    rw [this]
    have := mul_le_mul_of_nonpos_right ht hz
    nlinarith [Real.pi_pos]

theorem FL_hasDerivAt {a : ℝ} {φ : ℝ → ℂ} (h : TestFn a φ) (z : ℂ) :
    HasDerivAt (FL φ) (FL (fun t => φ t * (-(2 * π * I) * t)) z) z := by
  obtain ⟨B, hB⟩ := h.bdd
  exact hasDerivAt_expInt h.integrable hB _ z

theorem FL_deriv {a : ℝ} {φ : ℝ → ℂ} (h : TestFn a φ) (z : ℂ) :
    FL (deriv φ) z = (2 * π * I * z) * FL φ z := by
  obtain ⟨B, hB⟩ := h.bdd
  obtain ⟨B', hB'⟩ := h.deriv.bdd
  have hdiff : Differentiable ℝ φ := h.1.differentiable (by simp)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := φ) (u' := deriv φ)
    (v := fun t : ℝ => cexp (-(2 * π * I) * t * z))
    (v' := fun t : ℝ => (-(2 * π * I) * z) * cexp (-(2 * π * I) * t * z))
    (fun x _ => (hdiff x).hasDerivAt) (fun x _ => ?_) ?_ ?_ ?_
  · rw [FL, FL, ← integral_const_mul]
    have e1 : ∫ t : ℝ, deriv φ t * cexp (-(2 * π * I) * t * z)
        = - ∫ t : ℝ, φ t * ((-(2 * π * I) * z) * cexp (-(2 * π * I) * t * z)) := by
      rw [key, neg_neg]
    rw [e1, ← integral_neg]
    congr 1
    ext t
    ring
  · have h1 : HasDerivAt (fun t : ℝ => -(2 * π * I) * (t : ℂ) * z) (-(2 * π * I) * z) x := by
      have := ((hasDerivAt_id x).ofReal_comp.const_mul (-(2 * π * I))).mul_const z
      simpa using this
    have := h1.cexp
    exact this.congr_deriv (by ring)
  · have := (integrable_mul_exp h.integrable hB (-(2 * π * I)) z).const_mul (-(2 * π * I) * z)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; ring
  · exact integrable_mul_exp h.deriv.integrable hB' (-(2 * π * I)) z
  · exact integrable_mul_exp h.integrable hB (-(2 * π * I)) z

theorem FL_decay {a : ℝ} {φ : ℝ → ℂ} (h : TestFn a φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, z.im ≤ 0 →
      ‖FL φ z‖ * (1 + ‖z‖ ^ 3) ≤ K * rexp (2 * π * a * z.im) := by
  refine ⟨(∫ t, ‖φ t‖) + ∫ t, ‖deriv (deriv (deriv φ)) t‖, by positivity, fun z hz => ?_⟩
  have h0 := FL_norm_le h hz
  have h3 := FL_norm_le h.deriv.deriv.deriv hz
  rw [FL_deriv h.deriv.deriv, FL_deriv h.deriv, FL_deriv h] at h3
  have e : ‖2 * π * I * z * (2 * π * I * z * (2 * π * I * z * FL φ z))‖
      = (2 * π) ^ 3 * ‖z‖ ^ 3 * ‖FL φ z‖ := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_ofNat]
    ring
  rw [e] at h3
  have hpi : (1 : ℝ) ≤ (2 * π) ^ 3 := one_le_pow₀ (by nlinarith [Real.pi_gt_three])
  have h4 : ‖z‖ ^ 3 * ‖FL φ z‖ ≤ (2 * π) ^ 3 * ‖z‖ ^ 3 * ‖FL φ z‖ := by
    have : 0 ≤ ‖z‖ ^ 3 * ‖FL φ z‖ := by positivity
    nlinarith
  rw [add_mul, mul_add, mul_one]
  nlinarith



theorem contour_zero {G : ℂ → ℂ} (hG : Differentiable ℂ G) {K κ : ℝ} (hκ : 0 < κ) (hK : 0 ≤ K)
    (hb : ∀ z : ℂ, z.im ≤ 0 → ‖G z‖ ≤ K * rexp (κ * z.im) * (1 + z.re ^ 2)⁻¹) :
    ∫ x : ℝ, G x = 0 := by
  have hb' : ∀ (x y : ℝ), y ≤ 0 → ‖G (x + y * I)‖ ≤ K * rexp (κ * y) * (1 + x ^ 2)⁻¹ := by
    intro x y hy
    have := hb (x + y * I) (by simpa using hy)
    simpa using this
  have hint : ∀ y : ℝ, y ≤ 0 → Integrable (fun x : ℝ => G (x + y * I)) := by
    intro y hy
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (K * rexp (κ * y))) ?_
      (Eventually.of_forall fun x => hb' x y hy)
    exact (hG.continuous.comp (by fun_prop)).aestronglyMeasurable
  -- the integral on the line `Im = -R` equals the integral on the real line
  have hshift : ∀ R : ℝ, 0 < R → ∫ x : ℝ, G x = ∫ x : ℝ, G (x + (-R : ℝ) * I) := by
    intro R hR
    have h0 : Tendsto (fun X : ℝ => ∫ x in (-X)..X, G (x + (0 : ℝ) * I)) atTop
        (𝓝 (∫ x : ℝ, G (x + (0 : ℝ) * I))) :=
      intervalIntegral_tendsto_integral (hint 0 le_rfl) tendsto_neg_atTop_atBot tendsto_id
    have hR' : Tendsto (fun X : ℝ => ∫ x in (-X)..X, G (x + (-R : ℝ) * I)) atTop
        (𝓝 (∫ x : ℝ, G (x + (-R : ℝ) * I))) :=
      intervalIntegral_tendsto_integral (hint (-R) (by linarith)) tendsto_neg_atTop_atBot tendsto_id
    have hdiff : Tendsto (fun X : ℝ => (∫ x in (-X)..X, G (x + (0 : ℝ) * I)) -
        ∫ x in (-X)..X, G (x + (-R : ℝ) * I)) atTop (𝓝 0) := by
      apply squeeze_zero_norm (a := fun X : ℝ => 2 * (K * (1 + X ^ 2)⁻¹ * R))
      · intro X
        have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
          ((-X : ℝ) + (-R : ℝ) * I) ((X : ℝ) + (0 : ℝ) * I) hG.differentiableOn
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          add_im, mul_im, zero_add, add_zero, sub_self] at hc
        have hv : ∀ s : ℝ, ‖∫ y in (-R)..0, G (s + y * I)‖ ≤ K * (1 + s ^ 2)⁻¹ * R := by
          intro s
          have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -R) (b := 0)
            (C := K * (1 + s ^ 2)⁻¹) (f := fun y : ℝ => G (s + y * I)) (fun y hy => by
              rw [uIoc_of_le (by linarith)] at hy
              refine (hb' s y hy.2).trans ?_
              have : rexp (κ * y) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hy.2])
              have h2 : 0 ≤ (1 + s ^ 2)⁻¹ := by positivity
              calc K * rexp (κ * y) * (1 + s ^ 2)⁻¹ ≤ K * 1 * (1 + s ^ 2)⁻¹ := by gcongr
                _ = K * (1 + s ^ 2)⁻¹ := by ring)
          simpa [abs_of_pos hR] using this
        have e : (∫ x in (-X)..X, G (x + (0 : ℝ) * I)) - ∫ x in (-X)..X, G (x + (-R : ℝ) * I)
            = I • (∫ y in (-R)..0, G ((X : ℝ) + y * I)) - I • ∫ y in (-R)..0, G ((-X : ℝ) + y * I) := by
          linear_combination (-1 : ℂ) * hc
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_smul, Complex.norm_I, one_mul, one_mul]
        have h1 := hv X
        have h2 := hv (-X)
        rw [neg_sq] at h2
        linarith
      · have : Tendsto (fun X : ℝ => (1 + X ^ 2)⁻¹) atTop (𝓝 0) := by
          apply Tendsto.inv_tendsto_atTop
          exact tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by norm_num))
        simpa using ((this.const_mul K).mul_const R).const_mul 2
    have := tendsto_nhds_unique hdiff (h0.sub hR')
    have h3 : ∫ x : ℝ, G (x + (0 : ℝ) * I) = ∫ x : ℝ, G (x + (-R : ℝ) * I) := by
      rw [← sub_eq_zero]; exact this.symm
    simpa using h3
  have hbound : ∀ R : ℝ, 0 < R → ‖∫ x : ℝ, G x‖ ≤ K * π * rexp (-κ * R) := by
    intro R hR
    rw [hshift R hR]
    calc ‖∫ x : ℝ, G (x + (-R : ℝ) * I)‖ ≤ ∫ x : ℝ, K * rexp (κ * -R) * (1 + x ^ 2)⁻¹ :=
          norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
            (Eventually.of_forall fun x => hb' x (-R) (by linarith))
      _ = K * π * rexp (-κ * R) := by
          rw [integral_const_mul, integral_univ_inv_one_add_sq]; ring_nf
  have hlim : Tendsto (fun R : ℝ => K * π * rexp (-κ * R)) atTop (𝓝 0) := by
    have : Tendsto (fun R : ℝ => rexp (-κ * R)) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hκ) : Tendsto (fun R : ℝ => -κ * R) atTop atBot)
    simpa using this.const_mul (K * π)
  have : ‖∫ x : ℝ, G x‖ ≤ 0 :=
    ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun R hR => hbound R hR)
  exact norm_le_zero_iff.mp this



theorem primitive_real_bound {f h : ℂ → ℂ} (hh : ∀ z, HasDerivAt h (f z) z) (h0 : h 0 = 0)
    (hf : Continuous f) (hL2 : MemLp (fun x : ℝ => f x) 2) (x : ℝ) :
    ‖h x‖ ≤ (∫ t : ℝ, ‖f t‖ ^ 2) + |x| := by
  have hfc : Continuous (fun t : ℝ => f t) := hf.comp continuous_ofReal
  have hsq : Integrable (fun t : ℝ => ‖f t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).mp hL2
  have e : ∫ t in (0 : ℝ)..x, f t = h x := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
      (f := fun t : ℝ => h t) (f' := fun t : ℝ => f t)
      (fun t _ => (hh t).comp_ofReal) (hfc.intervalIntegrable _ _)
    simpa [h0] using this
  rw [← e]
  refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
  have hfin : volume (uIoc (0 : ℝ) x) ≠ ⊤ := by
    rw [uIoc, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hi1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (uIoc (0 : ℝ) x) :=
    integrableOn_const hfin
  calc ∫ t in uIoc (0 : ℝ) x, ‖f t‖ ≤ ∫ t in uIoc (0 : ℝ) x, (‖f t‖ ^ 2 + 1) := by
        exact setIntegral_mono_on ((hfc.norm.integrableOn_Icc (a := min 0 x)
          (b := max 0 x)).mono_set Ioc_subset_Icc_self)
          (hsq.integrableOn.add hi1) measurableSet_uIoc (fun t _ => by nlinarith [sq_nonneg (‖f t‖ - 1)])
    _ = (∫ t in uIoc (0 : ℝ) x, ‖f t‖ ^ 2) + ∫ t in uIoc (0 : ℝ) x, (1 : ℝ) :=
        integral_add hsq.integrableOn hi1
    _ ≤ (∫ t : ℝ, ‖f t‖ ^ 2) + |x| := by
        refine add_le_add (setIntegral_le_integral hsq
          (Eventually.of_forall fun t => by positivity)) ?_
        · rw [setIntegral_const, smul_eq_mul, mul_one, uIoc, Real.volume_real_Ioc]
          rcases le_total 0 x with hx | hx
          · simp [hx, abs_of_nonneg hx]
          · simp [hx, abs_of_nonpos hx]

theorem primitive_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A C : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hexp : ∀ z, ‖f z‖ ≤ C * rexp (A * ‖z‖)) (hL2 : MemLp (fun x : ℝ => f x) 2) :
    ∃ h : ℂ → ℂ, (∀ z, HasDerivAt h (f z) z) ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ z : ℂ, z.im ≤ 0 → ‖h z‖ ≤ M * (1 + ‖z‖) * rexp (-A * z.im) := by
  obtain ⟨h, h0, hh⟩ := hf.isExactOn_univ.with_val_at 0 0
  replace hh : ∀ z, HasDerivAt h (f z) z := fun z => hh z (mem_univ z)
  refine ⟨h, hh, ?_⟩
  set N : ℝ := ∫ t : ℝ, ‖f t‖ ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun t => by positivity
  have hreal : ∀ x : ℝ, ‖h x‖ ≤ N + |x| := primitive_real_bound hh h0 hf.continuous hL2
  have hgrow : ∀ z : ℂ, ‖h z‖ ≤ C * rexp (A * ‖z‖) * ‖z‖ := by
    intro z
    have := (convex_closedBall (0 : ℂ) ‖z‖).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := h) (f' := f) (C := C * rexp (A * ‖z‖)) (x := 0) (y := z)
      (fun w _ => (hh w).hasDerivWithinAt)
      (fun w hw => (hexp w).trans (by
        have : ‖w‖ ≤ ‖z‖ := by simpa using hw
        gcongr))
      (by simp) (by simp)
    simpa [h0] using this
  set v : ℂ → ℂ := fun w => h (-I * w) * cexp (-A * w) / (w + 1) with hv
  -- pointwise facts
  have hw1 : ∀ w : ℂ, 0 ≤ w.re → 1 ≤ ‖w + 1‖ := by
    intro w hw
    calc (1 : ℝ) ≤ (w + 1).re := by simp [hw]
      _ ≤ ‖w + 1‖ := Complex.re_le_norm _
  have hvnorm : ∀ w : ℂ, ‖v w‖ = ‖h (-I * w)‖ * rexp (-A * w.re) / ‖w + 1‖ := by
    intro w
    simp only [hv, norm_div, norm_mul, Complex.norm_exp]
    congr 3
    simp
  have hkey : ∀ (w : ℂ) (M : ℝ), 0 ≤ w.re → ‖h (-I * w)‖ * rexp (-A * w.re) ≤ M * ‖w + 1‖ →
      ‖v w‖ ≤ M := by
    intro w M hw hle
    rw [hvnorm, div_le_iff₀ (by linarith [hw1 w hw])]
    exact hle
  have hcl : closure {z : ℂ | 0 < z.re} ⊆ {z : ℂ | 0 ≤ z.re} :=
    closure_minimal (fun z (hz : 0 < z.re) => (le_of_lt hz : 0 ≤ z.re)) (isClosed_le continuous_const Complex.continuous_re)
  have hne : ∀ w : ℂ, 0 ≤ w.re → w + 1 ≠ 0 := by
    intro w hw h0'
    have := hw1 w hw
    rw [h0'] at this
    simp at this
    linarith
  have hhd : Differentiable ℂ h := fun z => (hh z).differentiableAt
  have hd : DiffContOnCl ℂ v {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    have hw' := hcl hw
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div
    · exact ((hhd _).comp w (by fun_prop)).mul (by fun_prop)
    · fun_prop
    · exact hne w hw'
  have hbig : ∀ w : ℂ, 0 ≤ w.re → ‖v w‖ ≤ N + 1 := by
    intro w hw
    apply PhragmenLindelof.right_half_plane_of_bounded_on_real hd ?_ ?_ ?_ hw
    · refine ⟨1, by norm_num, A + 1, ?_⟩
      apply Asymptotics.IsBigO.of_bound C
      rw [eventually_inf_principal]
      refine Eventually.of_forall fun w hw => ?_
      have hw' : 0 ≤ w.re := le_of_lt hw
      rw [Real.rpow_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      apply hkey w _ hw'
      have hnw : ‖-I * w‖ = ‖w‖ := by simp
      have h1 := hgrow (-I * w)
      rw [hnw] at h1
      have h2 : rexp (-A * w.re) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have h3 : ‖w‖ ≤ rexp ‖w‖ := by linarith [Real.add_one_le_exp ‖w‖]
      have h4 : rexp ((A + 1) * ‖w‖) = rexp (A * ‖w‖) * rexp ‖w‖ := by
        rw [← Real.exp_add]; ring_nf
      have h5 := hw1 w hw'
      calc ‖h (-I * w)‖ * rexp (-A * w.re) ≤ (C * rexp (A * ‖w‖) * ‖w‖) * 1 := by
            gcongr
        _ ≤ C * rexp (A * ‖w‖) * rexp ‖w‖ * 1 := by
            rw [mul_one, mul_one]; gcongr
        _ ≤ C * rexp (A * ‖w‖) * rexp ‖w‖ * ‖w + 1‖ := by
            gcongr
        _ = C * rexp ((A + 1) * ‖w‖) * ‖w + 1‖ := by rw [h4]; ring
    · refine ⟨C, ?_⟩
      rw [eventually_map]
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      apply hkey (x : ℂ) C (by simpa using hx.le)
      have h1 := hgrow (-I * x)
      have hnw : ‖-I * (x : ℂ)‖ = x := by simp [abs_of_pos hx]
      rw [hnw] at h1
      have h5 : x ≤ ‖(x : ℂ) + 1‖ := by
        calc x ≤ ((x : ℂ) + 1).re := by simp
          _ ≤ _ := Complex.re_le_norm _
      have h6 : rexp (A * x) * rexp (-A * (x : ℂ).re) = 1 := by
        rw [← Real.exp_add]; simp
      calc ‖h (-I * x)‖ * rexp (-A * (x : ℂ).re)
          ≤ (C * rexp (A * x) * x) * rexp (-A * (x : ℂ).re) := by gcongr
        _ = C * x * (rexp (A * x) * rexp (-A * (x : ℂ).re)) := by ring
        _ = C * x := by rw [h6, mul_one]
        _ ≤ C * ‖(x : ℂ) + 1‖ := by gcongr
    · intro x
      apply hkey (x * I) (N + 1) (by simp)
      have e1 : -I * (x * I) = (x : ℂ) := by
        rw [mul_comm (x : ℂ), ← mul_assoc]; simp
      have e2 : rexp (-A * ((x : ℂ) * I).re) = 1 := by simp
      rw [e1, e2, mul_one]
      have h1 := hreal x
      have h5 : 1 ≤ ‖(x : ℂ) * I + 1‖ := hw1 _ (by simp)
      have h6 : |x| ≤ ‖(x : ℂ) * I + 1‖ := by
        calc |x| = |((x : ℂ) * I + 1).im| := by simp
          _ ≤ _ := Complex.abs_im_le_norm _
      nlinarith
  refine ⟨N + 1, by linarith, fun z hz => ?_⟩
  have hw : 0 ≤ (I * z).re := by simpa using hz
  have h1 := hbig (I * z) hw
  rw [hvnorm, div_le_iff₀ (by linarith [hw1 _ hw])] at h1
  have e1 : -I * (I * z) = z := by rw [← mul_assoc]; simp
  have e2 : (I * z).re = -z.im := by simp
  rw [e1, e2] at h1
  have h2 : ‖I * z + 1‖ ≤ 1 + ‖z‖ := by
    calc ‖I * z + 1‖ ≤ ‖I * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 1 + ‖z‖ := by simp [add_comm]
  have h3 : rexp (-A * -z.im) * rexp (-A * z.im) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < rexp (-A * z.im) := Real.exp_pos _
  calc ‖h z‖ = ‖h z‖ * rexp (-A * -z.im) * rexp (-A * z.im) := by rw [mul_assoc, h3, mul_one]
    _ ≤ ((N + 1) * ‖I * z + 1‖) * rexp (-A * z.im) := by gcongr
    _ ≤ ((N + 1) * (1 + ‖z‖)) * rexp (-A * z.im) := by gcongr


theorem FL_differentiable {a : ℝ} {φ : ℝ → ℂ} (h : TestFn a φ) : Differentiable ℂ (FL φ) :=
  fun z => (FL_hasDerivAt h z).differentiableAt

theorem prod_bound {h : ℂ → ℂ} {A M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z : ℂ, z.im ≤ 0 → ‖h z‖ ≤ M * (1 + ‖z‖) * rexp (-A * z.im))
    {a : ℝ} {ψ : ℝ → ℂ} (hψ : TestFn a ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, z.im ≤ 0 →
      ‖h z * FL ψ z‖ ≤ K * rexp ((2 * π * a - A) * z.im) * (1 + z.re ^ 2)⁻¹ := by
  obtain ⟨K, hK, hKb⟩ := FL_decay hψ
  refine ⟨2 * M * K, by positivity, fun z hz => ?_⟩
  have h1 := hb z hz
  have h2 := hKb z hz
  have hr : 0 ≤ ‖z‖ := norm_nonneg z
  have hre : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← sq_abs z.re]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2
  have hpoly : (1 + ‖z‖) * (1 + z.re ^ 2) ≤ 2 * (1 + ‖z‖ ^ 3) := by
    have : (1 + ‖z‖) * (1 + z.re ^ 2) ≤ (1 + ‖z‖) * (1 + ‖z‖ ^ 2) := by gcongr
    nlinarith [mul_nonneg (sq_nonneg (‖z‖ - 1)) (by linarith : (0 : ℝ) ≤ ‖z‖ + 1)]
  have hE : rexp ((2 * π * a - A) * z.im) = rexp (-A * z.im) * rexp (2 * π * a * z.im) := by
    rw [← Real.exp_add]; ring_nf
  have hpos : (0 : ℝ) < 1 + z.re ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hpos, norm_mul, hE]
  have hE1 : 0 < rexp (-A * z.im) := Real.exp_pos _
  calc ‖h z‖ * ‖FL ψ z‖ * (1 + z.re ^ 2)
      ≤ (M * (1 + ‖z‖) * rexp (-A * z.im)) * ‖FL ψ z‖ * (1 + z.re ^ 2) := by gcongr
    _ = M * rexp (-A * z.im) * ‖FL ψ z‖ * ((1 + ‖z‖) * (1 + z.re ^ 2)) := by ring
    _ ≤ M * rexp (-A * z.im) * ‖FL ψ z‖ * (2 * (1 + ‖z‖ ^ 3)) := by gcongr
    _ = 2 * M * rexp (-A * z.im) * (‖FL ψ z‖ * (1 + ‖z‖ ^ 3)) := by ring
    _ ≤ 2 * M * rexp (-A * z.im) * (K * rexp (2 * π * a * z.im)) := by gcongr
    _ = 2 * M * K * (rexp (-A * z.im) * rexp (2 * π * a * z.im)) := by ring

theorem FL_real_bound {a : ℝ} {φ : ℝ → ℂ} (h : TestFn a φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, ‖FL φ x‖ ≤ K * (1 + x ^ 2)⁻¹ := by
  obtain ⟨K, hK, hKb⟩ := FL_decay h
  refine ⟨2 * K, by positivity, fun x => ?_⟩
  have h2 := hKb x (by simp)
  simp only [ofReal_im, mul_zero, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs] at h2
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hpos]
  have h3 : 1 + x ^ 2 ≤ 2 * (1 + |x| ^ 3) := by
    rw [← sq_abs x]
    nlinarith [abs_nonneg x, mul_nonneg (abs_nonneg x) (sq_nonneg (|x| - 1)), sq_nonneg (|x| - 1)]
  calc ‖FL φ x‖ * (1 + x ^ 2) ≤ ‖FL φ x‖ * (2 * (1 + |x| ^ 3)) := by gcongr
    _ = 2 * (‖FL φ x‖ * (1 + |x| ^ 3)) := by ring
    _ ≤ 2 * K := by gcongr

/-- The key orthogonality: `f` is orthogonal to Fourier transforms of test functions supported
to the right of `A / (2π)`. -/
theorem integral_mul_FL_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A C : ℝ} (hA : 0 < A)
    (hC : 0 < C) (hexp : ∀ z, ‖f z‖ ≤ C * rexp (A * ‖z‖)) (hL2 : MemLp (fun x : ℝ => f x) 2)
    {a : ℝ} (ha : A < 2 * π * a) {φ : ℝ → ℂ} (hφ : TestFn a φ) :
    ∫ x : ℝ, f x * FL φ x = 0 := by
  obtain ⟨h, hh, M, hM, hb⟩ := primitive_bound hf hA hC hexp hL2
  have hhd : Differentiable ℂ h := fun z => (hh z).differentiableAt
  set ψ : ℝ → ℂ := fun t => φ t * (-(2 * π * I) * t) with hψdef
  have hψ : TestFn a ψ := hφ.mul_lin _
  obtain ⟨K₁, hK₁, hb₁⟩ := prod_bound hM hb hψ
  obtain ⟨K₂, hK₂, hb₂⟩ := prod_bound hM hb hφ
  obtain ⟨K₃, hK₃, hb₃⟩ := FL_real_bound hφ
  have hfc : Continuous (fun t : ℝ => f t) := hf.continuous.comp continuous_ofReal
  have hsq : Integrable (fun t : ℝ => ‖f t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).mp hL2
  have hκ : 0 < 2 * π * a - A := by linarith
  have hzero : ∫ x : ℝ, h x * FL ψ x = 0 :=
    contour_zero (G := fun z => h z * FL ψ z) (hhd.mul (FL_differentiable hψ)) hκ hK₁ hb₁
  have hcont : ∀ {χ : ℝ → ℂ}, TestFn a χ → Continuous (fun x : ℝ => FL χ x) := fun hχ =>
    (FL_differentiable hχ).continuous.comp continuous_ofReal
  have hhc : Continuous (fun x : ℝ => h x) := hhd.continuous.comp continuous_ofReal
  have hint : ∀ {χ : ℝ → ℂ} {K : ℝ}, TestFn a χ → (∀ z : ℂ, z.im ≤ 0 →
      ‖h z * FL χ z‖ ≤ K * rexp ((2 * π * a - A) * z.im) * (1 + z.re ^ 2)⁻¹) →
      Integrable (fun x : ℝ => h x * FL χ x) := by
    intro χ K hχ hbχ
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul K)
      (hhc.mul (hcont hχ)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    simpa using hbχ x (by simp)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x : ℝ => h x)
    (u' := fun x : ℝ => f x) (v := fun x : ℝ => FL φ x) (v' := fun x : ℝ => FL ψ x)
    (fun x _ => (hh x).comp_ofReal) (fun x _ => (FL_hasDerivAt hφ x).comp_ofReal)
    (hint hψ hb₁) ?_ (hint hφ hb₂)
  · have : ∫ x : ℝ, f x * FL φ x = -∫ x : ℝ, h x * FL ψ x := by
      rw [key, neg_neg]
    rw [this, hzero, neg_zero]
  · refine Integrable.mono' (hsq.add (integrable_inv_one_add_sq.const_mul (K₃ ^ 2)))
      (hfc.mul (hcont hφ)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have h3 := hb₃ x
    have hinv : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    have hinv0 : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
    have h4 : ‖FL φ x‖ ^ 2 ≤ K₃ ^ 2 * (1 + x ^ 2)⁻¹ := by
      calc ‖FL φ x‖ ^ 2 ≤ (K₃ * (1 + x ^ 2)⁻¹) ^ 2 := by gcongr
        _ = K₃ ^ 2 * ((1 + x ^ 2)⁻¹ * (1 + x ^ 2)⁻¹) := by ring
        _ ≤ K₃ ^ 2 * ((1 + x ^ 2)⁻¹ * 1) := by gcongr
        _ = _ := by ring
    simp only [Pi.mul_apply, norm_mul, Pi.add_apply]
    nlinarith [sq_nonneg (‖f x‖ - ‖FL φ x‖), norm_nonneg (f x), norm_nonneg (FL φ x)]

theorem fourier_eq_FL (φ : ℝ → ℂ) (w : ℝ) : 𝓕 φ w = FL φ w := by
  rw [Real.fourier_real_eq_integral_exp_smul, FL]
  congr 1
  ext t
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

theorem FL_neg (φ : ℝ → ℂ) (z : ℂ) : FL φ (-z) = FL (fun t => φ (-t)) z := by
  rw [FL, FL, ← integral_neg_eq_self]
  congr 1
  ext t
  congr 2
  push_cast
  ring

/-- Orthogonality in terms of real test functions supported in `(A / (2π), ∞)`. -/
theorem supp_core {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A C : ℝ} (hA : 0 < A)
    (hC : 0 < C) (hexp : ∀ z, ‖f z‖ ≤ C * rexp (A * ‖z‖)) (hL2 : MemLp (fun x : ℝ => f x) 2)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    (hs : tsupport ρ ⊆ Ioi (A / (2 * π))) :
    ∫ x : ℝ, f x * FL (fun t => (ρ t : ℂ)) x = 0 := by
  have hc' : HasCompactSupport (fun x => (ρ x : ℂ)) :=
    hc.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hd : ContDiff ℝ ∞ (fun x => (ρ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hρ
  obtain ⟨a, ha, hav⟩ : ∃ a : ℝ, A / (2 * π) < a ∧ ∀ t, t < a → ρ t = 0 := by
    rcases (tsupport ρ).eq_empty_or_nonempty with he | hne
    · refine ⟨A / (2 * π) + 1, by linarith, fun t _ => ?_⟩
      by_contra h0
      have : t ∈ tsupport ρ := subset_tsupport _ h0
      rw [he] at this
      exact this
    · refine ⟨sInf (tsupport ρ), hs (hc.isCompact.sInf_mem hne), fun t ht => ?_⟩
      by_contra h0
      have : t ∈ tsupport ρ := subset_tsupport _ h0
      exact absurd (csInf_le hc.isCompact.bddBelow this) (not_le.mpr ht)
  have h2 : A < 2 * π * a := by
    have hpi : (0 : ℝ) < 2 * π := by positivity
    rw [div_lt_iff₀ hpi] at ha
    linarith
  exact integral_mul_FL_eq_zero hf hA hC hexp hL2 h2
    (φ := fun t => (ρ t : ℂ)) ⟨hd, hc', fun t ht => by simp [hav t ht]⟩

/-- Pairing of the inverse `L²` Fourier transform of `f|ℝ` against a test function. -/
theorem pairing {f : ℂ → ℂ} (hL2 : MemLp (fun x : ℝ => f x) 2)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) :
    ∫ x, ρ x • ((𝓕⁻ (hL2.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
      = ∫ x : ℝ, f x * FL (fun t => (ρ t : ℂ)) (-x) := by
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  have hc' : HasCompactSupport (fun x => (ρ x : ℂ)) :=
    hc.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hd : ContDiff ℝ ∞ (fun x => (ρ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hρ
  set ψ : 𝓢(ℝ, ℂ) := hc'.toSchwartzMap hd with hψ
  have h1 : ∫ x, ρ x • ((𝓕⁻ (hL2.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
      = Lp.toTemperedDistribution (𝓕⁻ (hL2.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) ψ := by
    rw [Lp.toTemperedDistribution_apply]
    rfl
  rw [h1, ← Lp.fourierInv_toTemperedDistribution_eq, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hL2.coeFn_toLp] with x hx
  rw [hx, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, fourier_eq_FL, smul_eq_mul,
    mul_comm, ofReal_neg]
  rfl

theorem fourierInv_supp {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A C : ℝ} (hA : 0 < A)
    (hC : 0 < C) (hexp : ∀ z, ‖f z‖ ≤ C * rexp (A * ‖z‖)) (hL2 : MemLp (fun x : ℝ => f x) 2) :
    ∀ᵐ t : ℝ, A / (2 * π) < |t| →
      ((𝓕⁻ (hL2.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t = 0 := by
  set k : Lp ℂ 2 (volume : Measure ℝ) := 𝓕⁻ (hL2.toLp _) with hk
  have hloc : LocallyIntegrable (k : ℝ → ℂ) := (Lp.memLp k).locallyIntegrable (by norm_num)
  -- right half-line
  have hR : ∀ᵐ t : ℝ, t ∈ Ioi (A / (2 * π)) → (k : ℝ → ℂ) t = 0 := by
    apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc.locallyIntegrableOn _)
    intro ρ hρ hc hs
    rw [hk, pairing hL2 hρ hc]
    have hf' : Differentiable ℂ (fun z => f (-z)) := hf.comp differentiable_neg
    have hL2' : MemLp (fun x : ℝ => (fun z => f (-z)) x) 2 := by
      have := hL2.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
      refine this.congr_norm ?_ ?_
      · exact (hf'.continuous.comp continuous_ofReal).aestronglyMeasurable
      · exact Eventually.of_forall fun x => by simp
    have := supp_core hf' hA hC (fun z => by simpa using hexp (-z)) hL2' hρ hc hs
    rw [← this, ← integral_neg_eq_self]
    simp
  -- left half-line
  have hL : ∀ᵐ t : ℝ, t ∈ Iio (-(A / (2 * π))) → (k : ℝ → ℂ) t = 0 := by
    apply isOpen_Iio.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc.locallyIntegrableOn _)
    intro ρ hρ hc hs
    rw [hk, pairing hL2 hρ hc]
    have hρ' : ContDiff ℝ ∞ (fun t => ρ (-t)) := hρ.comp contDiff_neg
    have hc' : HasCompactSupport (fun t => ρ (-t)) := hc.comp_homeomorph (Homeomorph.neg ℝ)
    have hs' : tsupport (fun t => ρ (-t)) ⊆ Ioi (A / (2 * π)) := by
      have e := tsupport_comp_eq_preimage ρ (Homeomorph.neg ℝ)
      intro t ht
      have ht' : t ∈ tsupport (ρ ∘ (Homeomorph.neg ℝ)) := ht
      rw [e] at ht'
      have : -t < -(A / (2 * π)) := hs ht'
      simp only [mem_Ioi]
      linarith
    have := supp_core hf hA hC hexp hL2 hρ' hc' hs'
    rw [← this]
    congr 1
    ext x
    rw [FL_neg]
  filter_upwards [hR, hL] with t h1 h2 ht
  rcases lt_abs.mp ht with h | h
  · exact h1 h
  · exact h2 (by simp only [mem_Iio]; linarith)

/-- An entire function which agrees with `f` on the real line agrees with `f` everywhere. -/
theorem eq_of_eq_on_real {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ x : ℝ, f x = g x) : f = g := by
  apply AnalyticOnNhd.eq_of_frequently_eq (z₀ := 0)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg)
  have ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [Complex.ofReal_zero] at this
      exact this
    · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [mem_compl_iff, mem_singleton_iff, ofReal_eq_zero]
      exact this.ne'
  exact ht.frequently (Eventually.of_forall fun n => h _).frequently

theorem easy_direction {A : ℝ} (hA : 0 < A) {f : ℂ → ℂ} {F : ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Ioo (-A) A)))
    (hrep : ∀ z : ℂ, f z = ∫ x in (-A)..A, F x * cexp (I * x * z)) :
    (∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * rexp (A * ‖z‖)) ∧
      MemLp (fun x : ℝ => f x) 2 volume := by
  set G₀ : ℝ → ℂ := (Ioo (-A) A).indicator F with hG₀
  have hG2 : MemLp G₀ 2 := (memLp_indicator_iff_restrict measurableSet_Ioo).mpr hF
  have hG1 : Integrable G₀ :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (hF.integrable (by norm_num))
  have hB : ∀ t, A < |t| → G₀ t = 0 := by
    intro t ht
    apply indicator_of_notMem
    intro hmem
    have : |t| < A := abs_lt.mpr hmem
    linarith
  have hf' : ∀ z : ℂ, f z = ∫ t : ℝ, G₀ t * cexp (I * t * z) := by
    intro z
    rw [hrep, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
      ← integral_indicator measurableSet_Ioo]
    congr 1
    ext t
    rw [hG₀, indicator_mul_left]
  refine ⟨⟨(∫ t, ‖G₀ t‖) + 1, by positivity, fun z => ?_⟩, ?_⟩
  · rw [hf']
    calc ‖∫ t : ℝ, G₀ t * cexp (I * t * z)‖ ≤ ∫ t : ℝ, ‖G₀ t‖ * rexp (‖I‖ * |A| * ‖z‖) :=
          norm_integral_le_of_norm_le (hG1.norm.mul_const _)
            (Eventually.of_forall fun t => norm_mul_exp_le hB I z t)
      _ = (∫ t, ‖G₀ t‖) * rexp (A * ‖z‖) := by
          rw [integral_mul_const, Complex.norm_I, one_mul, abs_of_pos hA]
      _ ≤ ((∫ t, ‖G₀ t‖) + 1) * rexp (A * ‖z‖) := by
          gcongr; linarith
  · have hcont : Continuous (𝓕 G₀) := fourier_continuous hG1
    have h2 : MemLp (𝓕 G₀) 2 := (Lp.memLp _).ae_eq (fourier_L1L2 hG1 hG2)
    have hsq : Integrable (fun ξ : ℝ => ‖𝓕 G₀ ξ‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mp h2
    have hc : -(1 / (2 * π)) ≠ 0 := by
      have : (0 : ℝ) < 1 / (2 * π) := by positivity
      linarith
    have hsq' := hsq.comp_mul_left' hc
    have hcont' : Continuous (fun x : ℝ => 𝓕 G₀ (-(1 / (2 * π)) * x)) :=
      hcont.comp (by fun_prop)
    have h3 : MemLp (fun x : ℝ => 𝓕 G₀ (-(1 / (2 * π)) * x)) 2 :=
      (memLp_two_iff_integrable_sq_norm hcont'.aestronglyMeasurable).mpr hsq'
    have e : (fun x : ℝ => f x) = fun x : ℝ => 𝓕 G₀ (-(1 / (2 * π)) * x) := by
      ext x
      rw [hf', fourier_eq_FL, FL]
      congr 1
      ext t
      congr 2
      push_cast
      field_simp
    rw [e]
    exact h3

theorem hard_direction {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A C : ℝ} (hA : 0 < A)
    (hC : 0 < C) (hexp : ∀ z, ‖f z‖ ≤ C * rexp (A * ‖z‖)) (hL2 : MemLp (fun x : ℝ => f x) 2) :
    ∃ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Ioo (-A) A)) ∧
      ∀ z : ℂ, f z = ∫ x in (-A)..A, F x * cexp (I * x * z) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set α : ℝ := A / (2 * π) with hα
  have hα0 : 0 < α := by positivity
  set k : Lp ℂ 2 (volume : Measure ℝ) := 𝓕⁻ (hL2.toLp _) with hk
  have hk0 := fourierInv_supp hf hA hC hexp hL2
  rw [← hk, ← hα] at hk0
  set k₀ : ℝ → ℂ := (Icc (-α) α).indicator (k : ℝ → ℂ) with hk₀
  have hmeas : StronglyMeasurable k₀ := (Lp.stronglyMeasurable k).indicator measurableSet_Icc
  have hae : k₀ =ᵐ[volume] (k : ℝ → ℂ) := by
    filter_upwards [hk0] with t ht
    by_cases hmem : t ∈ Icc (-α) α
    · rw [hk₀, indicator_of_mem hmem]
    · rw [hk₀, indicator_of_notMem hmem]
      refine (ht ?_).symm
      by_contra hle
      exact hmem (abs_le.mp (not_lt.mp hle))
  have hk₀2 : MemLp k₀ 2 := (Lp.memLp k).ae_eq hae.symm
  have hk₀1 : Integrable k₀ :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (((Lp.memLp k).restrict (Icc (-α) α)).integrable (by norm_num))
  have hB : ∀ t, α < |t| → k₀ t = 0 := by
    intro t ht
    apply indicator_of_notMem
    intro hmem
    have : |t| ≤ α := abs_le.mpr hmem
    linarith
  have hLp : hk₀2.toLp k₀ = k := by
    rw [← Lp.toLp_coeFn k (Lp.memLp k)]
    exact MemLp.toLp_congr _ _ hae
  have hfou : (fun x : ℝ => f x) =ᵐ[volume] 𝓕 k₀ := by
    have h1 := fourier_L1L2 hk₀1 hk₀2
    rw [hLp, hk, fourier_fourierInv_eq] at h1
    exact hL2.coeFn_toLp.symm.trans h1
  have hreal : ∀ x : ℝ, f x = FL k₀ x := by
    intro x
    have := (Continuous.ae_eq_iff_eq (μ := (volume : Measure ℝ))
      (hf.continuous.comp continuous_ofReal) (fourier_continuous hk₀1)).mp hfou
    rw [← fourier_eq_FL]
    exact congrFun this x
  have hE : Differentiable ℂ (FL k₀) := fun z =>
    (hasDerivAt_expInt hk₀1 hB (-(2 * π * I)) z).differentiableAt
  have hfE : f = FL k₀ := eq_of_eq_on_real hf hE hreal
  refine ⟨fun u => (1 / (2 * π) : ℂ) * k₀ (-(1 / (2 * π)) * u), ?_, fun z => ?_⟩
  · apply MemLp.restrict
    have hc : -(1 / (2 * π)) ≠ 0 := by
      have : (0 : ℝ) < 1 / (2 * π) := by positivity
      linarith
    have hsq : Integrable (fun t : ℝ => ‖k₀ t‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mp hk₀2
    have hm : StronglyMeasurable (fun u : ℝ => (1 / (2 * π) : ℂ) * k₀ (-(1 / (2 * π)) * u)) :=
      (hmeas.comp_measurable (measurable_const_mul _)).const_mul _
    rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
    refine ((hsq.comp_mul_left' hc).const_mul (‖(1 / (2 * π) : ℂ)‖ ^ 2)).congr
      (Eventually.of_forall fun u => ?_)
    simp only [norm_mul, mul_pow]
  · set W : ℝ → ℂ := fun u => (1 / (2 * π) : ℂ) * k₀ (-(1 / (2 * π)) * u) * cexp (I * u * z)
      with hW
    have hW0 : ∀ u, u ∉ Icc (-A) A → W u = 0 := by
      intro u hu
      have : k₀ (-(1 / (2 * π)) * u) = 0 := by
        apply hB
        by_contra hle
        apply hu
        have h1 : |(-(1 / (2 * π)) * u)| = |u| / (2 * π) := by
          rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
          ring
        rw [h1, hα, not_lt, div_le_div_iff_of_pos_right hpi] at hle
        exact abs_le.mp hle
      show (1 / (2 * π) : ℂ) * k₀ (-(1 / (2 * π)) * u) * cexp (I * u * z) = 0
      rw [this]; simp
    have h1 : ∫ u in (-A)..A, W u = ∫ u, W u := by
      rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
        setIntegral_eq_integral_of_forall_compl_eq_zero hW0]
    have h2 := Measure.integral_comp_mul_left W (-(2 * π))
    have h3 : ∫ t : ℝ, W (-(2 * π) * t) = (1 / (2 * π) : ℂ) * FL k₀ z := by
      rw [FL, ← integral_const_mul]
      congr 1
      ext t
      simp only [hW]
      have e1 : -(1 / (2 * π)) * (-(2 * π) * t) = t := by field_simp
      rw [e1]
      push_cast
      ring_nf
    rw [h3] at h2
    have h4 : |(-(2 * π))⁻¹| = 1 / (2 * π) := by
      rw [abs_inv, abs_neg, abs_of_pos hpi, one_div]
    rw [h4] at h2
    change f z = ∫ u in (-A)..A, W u
    rw [h1, hfE]
    have hne : (2 * π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    have h5 : (1 / (2 * π) : ℂ) * FL k₀ z = (1 / (2 * π) : ℂ) * ∫ u, W u := by
      rw [h2, Complex.real_smul]; push_cast; ring
    exact mul_left_cancel₀ (one_div_ne_zero hne) h5

end MasulloGRHPaleyWienerAux

theorem solution (A : ℝ) (hA : 0 < A) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) :
    (∃ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Set.Ioo (-A) A)) ∧
      ∀ z : ℂ, f z = ∫ x in (-A)..A, F x * Complex.exp (Complex.I * x * z)) ↔
    ((∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)) ∧
      MemLp (fun x : ℝ => f x) 2 volume) := by
  constructor
  · rintro ⟨F, hF, hrep⟩
    exact MasulloGRHPaleyWienerAux.easy_direction hA hF hrep
  · rintro ⟨⟨C, hC, hexp⟩, hL2⟩
    exact MasulloGRHPaleyWienerAux.hard_direction hf hA hC hexp hL2
