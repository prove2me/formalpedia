-- Prove2me | solution 1 for MasulloRH.shrinking_compact_test_mellin_zero_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:35:24.577405+00:00
-- url     : https://prove2.me/submissions/bf56004e-da1f-46b6-8d4f-5ed0e73681d3

import Mathlib
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_weighted_positive_zeta_zeros_schwartz_scaling

open Set MeasureTheory FourierTransform Filter
open scoped FourierTransform SchwartzMap Topology ContDiff

namespace MasulloAudit

/-- The difference between a test and its real exponential tilt. -/
private noncomputable def tiltDifference (h : 𝓢(ℝ, ℂ)) (a x : ℝ) : ℂ :=
  ((Real.exp (a*x) - 1 : ℝ) : ℂ) * h x

private lemma tiltDifference_contDiff (h : 𝓢(ℝ, ℂ)) (a : ℝ) :
    ContDiff ℝ ∞ (tiltDifference h a) := by
  unfold tiltDifference
  have he : ContDiff ℝ ∞ (fun x : ℝ ↦ Real.exp (a*x) - 1) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp he).mul h.smooth'

private lemma tiltDifference_tsupport (h : 𝓢(ℝ, ℂ)) (a : ℝ) :
    tsupport (tiltDifference h a) ⊆ tsupport h := by
  unfold tiltDifference
  exact tsupport_mul_subset_right

private lemma iteratedDeriv_tsupport {g : ℝ → ℂ} (n : ℕ) :
    tsupport (iteratedDeriv n g) ⊆ tsupport g := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

private lemma integrable_iteratedDeriv_compact {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (n : ℕ) : Integrable (iteratedDeriv n g) :=
  (hg.continuous_iteratedDeriv n (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact hc
      ((subset_tsupport _).trans (iteratedDeriv_tsupport n)))

private lemma hasDerivAt_realExp_mul_ofReal (a x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (Real.exp (a*y) : ℂ)) ((a*Real.exp (a*x) : ℝ) : ℂ) x := by
  have h := (Real.hasDerivAt_exp (a*x)).comp x ((hasDerivAt_id x).const_mul a)
  have hf : HasDerivAt (fun y : ℝ ↦ Real.exp (a*y)) (a*Real.exp (a*x)) x := by
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using! h
  exact hf.ofReal_comp

private lemma tiltDifference_deriv_two (h : 𝓢(ℝ, ℂ)) (a x : ℝ) :
    iteratedDeriv 2 (tiltDifference h a) x =
      ((Real.exp (a*x) - 1 : ℝ) : ℂ) * iteratedDeriv 2 h x +
        ((2*a*Real.exp (a*x) : ℝ) : ℂ) * deriv h x +
        ((a^2*Real.exp (a*x) : ℝ) : ℂ) * h x := by
  let e (x : ℝ) : ℂ := Real.exp (a*x)
  have he (x : ℝ) : HasDerivAt e ((a:ℂ)*e x) x := by
    simpa only [e, Complex.ofReal_mul] using hasDerivAt_realExp_mul_ofReal a x
  have h1 : deriv (tiltDifference h a) = fun x ↦ ((a:ℂ)*e x)*h x + (e x-1)*deriv h x := by
    funext x
    have hD := ((he x).sub_const 1).mul (h.differentiable x).hasDerivAt
    rw [show tiltDifference h a = (fun y ↦ (e y-1)*h y) from by
      funext y; simp only [tiltDifference,e,Complex.ofReal_sub,Complex.ofReal_one]]
    exact hD.deriv
  rw [show (2 : ℕ) = 1+1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one, h1]
  have hd : Differentiable ℝ (deriv h) := (contDiff_infty_iff_deriv.mp h.smooth').2.differentiable (by simp)
  have hD1 := ((he x).const_mul (a:ℂ)).mul (h.differentiable x).hasDerivAt
  have hD2 := ((he x).sub_const 1).mul (hd x).hasDerivAt
  have hD := (hD1.add hD2).deriv
  have hEq : deriv (fun x : ℝ ↦ ((a:ℂ)*e x)*h x + (e x-1)*deriv h x) x = _ := hD
  rw [hEq]
  simp only [e, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_pow]
  ring

private lemma integral_norm_supportBound {f : ℝ → ℂ} (hf : Integrable f)
    {R C : ℝ} (hR : 0 ≤ R) (hSupport : tsupport f ⊆ Icc (-R) R)
    (hBound : ∀ x ∈ Icc (-R) R, ‖f x‖ ≤ C) :
    (∫ x : ℝ, ‖f x‖) ≤ 2*R*C := by
  let K := Icc (-R) R
  have hz (x : ℝ) (hx : x ∉ K) : ‖f x‖ = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hSupport h)), norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ ≤ ∫ _ in K, C := setIntegral_mono_on hf.norm.integrableOn
      (integrableOn_const isCompact_Icc.measure_lt_top.ne) measurableSet_Icc hBound
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, show K = Icc (-R) R from rfl,
        Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring

private lemma norm_fourier_le_integral_norm_real (g : ℝ → ℂ) (ξ : ℝ) :
    ‖𝓕 g ξ‖ ≤ ∫ x : ℝ, ‖g x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ) g ξ

private lemma weighted_norm_fourier_le_second_deriv {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (ξ : ℝ) :
    ξ^2 * ‖𝓕 g ξ‖ ≤ ∫ x : ℝ, ‖iteratedDeriv 2 g x‖ := by
  have hs := norm_fourier_le_integral_norm_real (iteratedDeriv 2 g) ξ
  have he := congrFun (Real.fourier_iteratedDeriv (n := 2) (N := ⊤) (hf := by exact hg)
    (fun n _ ↦ integrable_iteratedDeriv_compact hg hc n) (by simp)) ξ
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hNorm : ‖(2*Real.pi*Complex.I*(ξ:ℂ))^2 • 𝓕 g ξ‖ =
      ((2*Real.pi)^2)*ξ^2 * ‖𝓕 g ξ‖ := by
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_ofNat,
      Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one,
      abs_of_pos Real.pi_pos]
    ring_nf
    rw [sq_abs]
    ring
  rw [he, hNorm] at hs
  exact (le_mul_of_one_le_left (by positivity : 0 ≤ ξ^2 * ‖𝓕 g ξ‖)
    (one_le_pow₀ hπ)).trans (by simpa only [mul_assoc] using hs)


private lemma norm_exp_parameters {R a x : ℝ} (hR : 1 ≤ R)
    (ha : |a| *R ≤ 1) (hx : x ∈ Icc (-R) R) :
    |a| ≤ 1 ∧ |Real.exp (a*x)-1| ≤ 2*R*|a| ∧ Real.exp (a*x) ≤ Real.exp 1 := by
  have hA : |a| ≤ 1 := (le_mul_of_one_le_right (abs_nonneg _) hR).trans ha
  have hX : |a*x| ≤ |a| *R := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr hx) (abs_nonneg _)
  refine ⟨hA, ?_, Real.exp_le_exp.mpr ((le_abs_self _).trans (hX.trans ha))⟩
  calc
    _ ≤ 2*|a*x| := Real.abs_exp_sub_one_le (hX.trans ha)
    _ ≤ 2*(|a| *R) := mul_le_mul_of_nonneg_left hX (by norm_num)
    _ = _ := by ring

private lemma uniform_test_derivative_bound (h : 𝓢(ℝ, ℂ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
      ‖h x‖ ≤ B ∧ ‖deriv h x‖ ≤ B ∧ ‖iteratedDeriv 2 h x‖ ≤ B := by
  let Q := fun n : ℕ ↦ SchwartzMap.seminorm ℝ 0 n h
  refine ⟨Q 0+Q 1+Q 2, by positivity, fun x ↦ ?_⟩
  have h0 : ‖h x‖ ≤ Q 0 := SchwartzMap.norm_le_seminorm ℝ h x
  have h1 : ‖deriv h x‖ ≤ Q 1 := by
    rw [norm_deriv_eq_norm_fderiv, ← norm_iteratedFDeriv_one]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ h 1 x
  have h2 : ‖iteratedDeriv 2 h x‖ ≤ Q 2 := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ h 2 x
  have hQ0 : 0 ≤ Q 0 := by positivity
  have hQ1 : 0 ≤ Q 1 := by positivity
  have hQ2 : 0 ≤ Q 2 := by positivity
  exact ⟨h0.trans (by linarith),h1.trans (by linarith),h2.trans (by linarith)⟩

private lemma tilt_bounds_on_supportBall (h : 𝓢(ℝ, ℂ)) {R a B x : ℝ}
    (hR : 1 ≤ R) (ha : |a| *R ≤ 1) (hx : x ∈ Icc (-R) R)
    (h0 : ‖h x‖ ≤ B) (h1 : ‖deriv h x‖ ≤ B) (h2 : ‖iteratedDeriv 2 h x‖ ≤ B) :
    ‖tiltDifference h a x‖ ≤ 2*R*B*|a| ∧
    ‖iteratedDeriv 2 (tiltDifference h a) x‖ ≤ (2*R+3*Real.exp 1)*B*|a| := by
  obtain ⟨ha1,hE,hExp⟩ := norm_exp_parameters hR ha hx
  have hB : 0 ≤ B := (norm_nonneg _).trans h0
  have hS0 : 0 ≤ 2*R*|a| := by positivity
  have hS1 : 0 ≤ 2*|a| *Real.exp 1 := by positivity
  have hS2 : 0 ≤ |a| *Real.exp 1 := by positivity
  have hU0 : ‖((Real.exp (a*x)-1 : ℝ):ℂ)‖ ≤ 2*R*|a| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hE
  have hU1 : ‖((2*a*Real.exp (a*x) : ℝ):ℂ)‖ ≤ 2*|a| *Real.exp 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ)), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left hExp (by positivity)
  have hU2 : ‖((a^2*Real.exp (a*x) : ℝ):ℂ)‖ ≤ |a| *Real.exp 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    have hPow : |a|^2 ≤ |a| := by rw [pow_two]; exact mul_le_of_le_one_left (abs_nonneg _) ha1
    exact mul_le_mul hPow hExp (by positivity) (by positivity)
  constructor
  · unfold tiltDifference
    rw [norm_mul]
    calc _ ≤ (2*R*|a|)*B := mul_le_mul hU0 h0 (norm_nonneg _) hS0
         _ = _ := by ring
  · rw [tiltDifference_deriv_two]
    let u0 := ((Real.exp (a*x)-1 : ℝ):ℂ) * iteratedDeriv 2 h x
    let u1 := ((2*a*Real.exp (a*x) : ℝ):ℂ) * deriv h x
    let u2 := ((a^2*Real.exp (a*x) : ℝ):ℂ) * h x
    have hb0 : ‖u0‖ ≤ (2*R*|a|)*B := by
      dsimp only [u0]
      rw [norm_mul]
      exact mul_le_mul hU0 h2 (norm_nonneg _) hS0
    have hb1 : ‖u1‖ ≤ (2*|a| *Real.exp 1)*B := by
      dsimp only [u1]
      rw [norm_mul]
      exact mul_le_mul hU1 h1 (norm_nonneg _) hS1
    have hb2 : ‖u2‖ ≤ (|a| *Real.exp 1)*B := by
      dsimp only [u2]
      rw [norm_mul]
      exact mul_le_mul hU2 h0 (norm_nonneg _) hS2
    calc
      _ = ‖u0+u1+u2‖ := rfl
      _ ≤ ‖u0‖ + ‖u1‖ + ‖u2‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (2*R*|a|)*B + (2*|a| *Real.exp 1)*B + (|a| *Real.exp 1)*B :=
        add_le_add (add_le_add hb0 hb1) hb2
      _ = _ := by ring

/-- A real exponential tilt of a smooth compact test changes its Fourier transform by
an absolutely summable envelope, uniformly for sufficiently small tilts. -/
theorem norm_fourier_tiltDifference_le (h : 𝓢(ℝ, ℂ)) (hC : HasCompactSupport h) :
    ∃ R ≥ (1:ℝ), ∃ C ≥ (0:ℝ), ∀ a ξ : ℝ, |a| *R ≤ 1 →
      ‖𝓕 (tiltDifference h a) ξ‖ ≤ C*|a|/(1+ξ^2) := by
  obtain ⟨R0, hR0, hSup⟩ := hC.isBounded.exists_pos_norm_le
  let R := max 1 R0
  have hR : 1 ≤ R := le_max_left _ _
  have hSupport : tsupport h ⊆ Icc (-R) R := fun x hx ↦
    abs_le.mp (by rw [← Real.norm_eq_abs]; exact (hSup x hx).trans (le_max_right _ _))
  obtain ⟨B,hB,hDer⟩ := uniform_test_derivative_bound h
  let C0 := 2*R*(2*R*B)
  let C2 := 2*R*((2*R+3*Real.exp 1)*B)
  refine ⟨R,hR,C0+C2,by positivity,fun a ξ ha ↦ ?_⟩
  let g := tiltDifference h a
  have hg : ContDiff ℝ ∞ g := tiltDifference_contDiff h a
  have hSub : tsupport g ⊆ tsupport h := tiltDifference_tsupport h a
  have hgC : HasCompactSupport g := HasCompactSupport.of_support_subset_isCompact hC
    ((subset_tsupport _).trans hSub)
  have hi0 : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgC
  have hi2 : Integrable (iteratedDeriv 2 g) := integrable_iteratedDeriv_compact hg hgC 2
  have hBd (x : ℝ) (hx : x ∈ Icc (-R) R) :=
    tilt_bounds_on_supportBall h hR ha hx (hDer x).1 (hDer x).2.1 (hDer x).2.2
  have hA : ‖𝓕 g ξ‖ ≤ C0*|a| := by
    calc
      _ ≤ ∫ x : ℝ, ‖g x‖ := norm_fourier_le_integral_norm_real g ξ
      _ ≤ 2*R*(2*R*B*|a|) :=
        integral_norm_supportBound hi0 (by positivity) (hSub.trans hSupport)
          (fun x hx ↦ (hBd x hx).1)
      _ = _ := by unfold C0; ring
  have hD : ξ^2 * ‖𝓕 g ξ‖ ≤ C2*|a| := by
    calc
      _ ≤ ∫ x : ℝ, ‖iteratedDeriv 2 g x‖ := weighted_norm_fourier_le_second_deriv hg hgC ξ
      _ ≤ 2*R*((2*R+3*Real.exp 1)*B*|a|) :=
        integral_norm_supportBound hi2 (by positivity)
          ((iteratedDeriv_tsupport 2).trans (hSub.trans hSupport))
          (fun x hx ↦ (hBd x hx).2)
      _ = _ := by unfold C2; ring
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = ‖𝓕 g ξ‖ + ξ^2*‖𝓕 g ξ‖ := by ring
    _ ≤ C0*|a| + C2*|a| := add_le_add hA hD
    _ = _ := by ring



/-- The Mellin pairing in the logarithmic variable of a shrinking test. -/
noncomputable def shrinkingMellin (f : 𝓢(ℝ, ℂ)) (ε : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp ((ε : ℂ)*(z-1/2)*(x:ℂ)) * f x

private lemma integrable_exp_linear_mul_test (f : 𝓢(ℝ, ℂ)) (hf : HasCompactSupport f) (s : ℂ) :
    Integrable (fun x : ℝ ↦ Complex.exp (s*(x:ℂ))*f x) := by
  have hC : Continuous (fun x : ℝ ↦ Complex.exp (s*(x:ℂ))*f x) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul f.continuous
  exact hC.integrable_of_hasCompactSupport (hf.mul_left)

private lemma integrable_fourier_integrand (f : 𝓢(ℝ, ℂ)) (hf : HasCompactSupport f) (ξ : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (↑(-2*Real.pi*x*ξ) * Complex.I) * f x) := by
  have hI := integrable_exp_linear_mul_test f hf (↑(-2*Real.pi*ξ)*Complex.I)
  refine hI.congr ?_
  filter_upwards [] with x
  congr 2
  push_cast
  ring

private lemma shrinkingMellin_sub_fourier_eq (f : 𝓢(ℝ, ℂ)) (hf : HasCompactSupport f)
    (ε : ℝ) (z : ℂ) :
    shrinkingMellin f ε z - 𝓕 (f : ℝ → ℂ) (-ε*z.im/(2*Real.pi)) =
      𝓕 (tiltDifference f (ε*(z.re-1/2))) (-ε*z.im/(2*Real.pi)) := by
  let ξ : ℝ := -ε*z.im/(2*Real.pi)
  let a : ℝ := ε*(z.re-1/2)
  rw [shrinkingMellin, Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_sub (integrable_exp_linear_mul_test f hf _) (integrable_fourier_integrand f hf ξ)]
  refine integral_congr_ae ?_
  filter_upwards [] with x
  change Complex.exp ((ε:ℂ)*(z-1/2)*(x:ℂ))*f x -
    Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)*f x =
    Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)*tiltDifference f a x
  have hPhase : -2*Real.pi*x*ξ = ε*z.im*x := by
    unfold ξ
    field_simp [Real.pi_ne_zero]
  have hZ : ((ε:ℂ)*(z-1/2)*(x:ℂ)) =
      (a*x:ℝ) + ↑(-2*Real.pi*x*ξ)*Complex.I := by
    rw [hPhase]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, Complex.add_re, add_zero]
      unfold a
      ring
    · simp only [Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.sub_re,
        Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, Complex.add_im, zero_add, add_zero, mul_one]
      ring
  rw [hZ, Complex.exp_add, tiltDifference, Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_one]
  ring

/-- Uniform strip comparison between the true Mellin weight and the
critical-line additive Fourier weight for compact smooth tests. -/
theorem shrinkingMellin_uniform_strip_error (f : 𝓢(ℝ, ℂ)) (hf : HasCompactSupport f) :
    ∃ ε₀ > (0:ℝ), ε₀ ≤ 1 ∧ ∃ C ≥ (0:ℝ),
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
        ‖shrinkingMellin f ε z - 𝓕 (f : ℝ → ℂ) (-ε*z.im/(2*Real.pi))‖ ≤
          C*ε/(1+(ε*z.im/(2*Real.pi))^2) := by
  obtain ⟨R,hR,C,hC,hB⟩ := norm_fourier_tiltDifference_le f hf
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  refine ⟨R⁻¹, inv_pos.mpr hR0, inv_le_one_of_one_le₀ hR, C,hC,?_⟩
  intro ε hε hε₀ z h0 h1
  have hA : |ε*(z.re-1/2)| ≤ ε := by
    rw [abs_mul, abs_of_pos hε]
    have hD : |z.re-1/2| ≤ (1:ℝ) := by rw [abs_le]; constructor <;> linarith
    exact mul_le_of_le_one_right hε.le hD
  have hA' : |ε*(z.re-1/2)| *R ≤ 1 := by
    calc
      _ ≤ ε*R := mul_le_mul_of_nonneg_right hA hR0.le
      _ ≤ R⁻¹*R := mul_le_mul_of_nonneg_right hε₀ hR0.le
      _ = _ := inv_mul_cancel₀ hR0.ne'
  rw [shrinkingMellin_sub_fourier_eq f hf]
  calc
    _ ≤ C*|ε*(z.re-1/2)|/(1+(-ε*z.im/(2*Real.pi))^2) := hB _ _ hA'
    _ ≤ _ := by
      have hSign : -ε*z.im/(2*Real.pi) = -(ε*z.im/(2*Real.pi)) := by ring
      rw [hSign, neg_sq]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA hC) (by positivity)


end MasulloAudit

open MeasureTheory Filter Set FourierTransform
open scoped Topology SchwartzMap FourierTransform

namespace MasulloAudit

private abbrev PositiveZero :=
  {z : ℂ // Zeta23.IsNontrivialZero z ∧ 0 < z.im}

private noncomputable def complexSchwartzTest (h : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℂ) :=
  h.postcompCLM Complex.ofRealCLM

private lemma complexSchwartzTest_apply (h : 𝓢(ℝ, ℝ)) (x : ℝ) :
    complexSchwartzTest h x = (h x : ℂ) := rfl

private lemma hasCompactSupport_complexSchwartzTest (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    HasCompactSupport (complexSchwartzTest h) := by
  have he : Function.support (complexSchwartzTest h) = Function.support h := by
    ext x
    simp [Function.mem_support, complexSchwartzTest_apply]
  unfold HasCompactSupport tsupport at *
  rwa [he]

private noncomputable def reFourierTest (h : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℝ) :=
  (𝓕 (complexSchwartzTest h)).postcompCLM Complex.reCLM

private lemma reFourierTest_apply (h : 𝓢(ℝ, ℝ)) (ξ : ℝ) :
    reFourierTest h ξ = (𝓕 (complexSchwartzTest h : ℝ → ℂ) ξ).re := rfl

private lemma reFourierTest_eq_cos (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) (ξ : ℝ) :
    reFourierTest h ξ = ∫ x : ℝ, Real.cos (-2*Real.pi*x*ξ)*h x := by
  let f := complexSchwartzTest h
  have hfC := hasCompactSupport_complexSchwartzTest h hC
  have hC : Continuous (fun x : ℝ ↦ Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)*f x) := by
    have hx : Continuous (fun x : ℝ ↦ -2*Real.pi*x*ξ) := by fun_prop
    exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hx).mul_const _)).mul f.continuous
  have hI := hC.integrable_of_hasCompactSupport (μ := volume) hfC.mul_left
  have he := integral_re (𝕜 := ℂ) hI
  change (∫ x : ℝ, (Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)*f x).re) =
    (∫ x : ℝ, Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)*f x).re at he
  rw [reFourierTest_apply, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  change (Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)*complexSchwartzTest h x).re = _
  rw [complexSchwartzTest_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

private lemma reFourierTest_even (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    Function.Even (reFourierTest h) := by
  intro ξ
  rw [reFourierTest_eq_cos h hC, reFourierTest_eq_cos h hC]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show -2*Real.pi*x*(-ξ) = -(-2*Real.pi*x*ξ) by ring, Real.cos_neg]

private lemma reFourierTest_integral (h : 𝓢(ℝ, ℝ)) :
    (∫ ξ : ℝ, reFourierTest h ξ) = h 0 := by
  let f := complexSchwartzTest h
  have hF : Integrable (𝓕 (f : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 f).integrable
  have hInv := f.integrable.fourierInv_fourier_eq hF (v := (0:ℝ)) f.continuous.continuousAt
  rw [Real.fourierInv_eq] at hInv
  have hAll : (∫ ξ : ℝ, 𝓕 (f : ℝ → ℂ) ξ) = f 0 := by
    simpa only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] using hInv
  have he := integral_re (𝕜 := ℂ) hF
  change (∫ ξ : ℝ, (𝓕 (f : ℝ → ℂ) ξ).re) = (∫ ξ : ℝ, 𝓕 (f : ℝ → ℂ) ξ).re at he
  simp only [reFourierTest_apply]
  rw [he, hAll]
  exact Complex.ofReal_re _

private lemma integral_positive_reFourierTest (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    (∫ ξ in Ioi (0:ℝ), reFourierTest h ξ) = h 0 / 2 := by
  let F := reFourierTest h
  have hE : (∫ ξ in Iic (0:ℝ), F ξ) = ∫ ξ in Ioi (0:ℝ), F ξ := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    simp only [neg_zero]
    exact setIntegral_congr_fun measurableSet_Ioi (fun ξ _ ↦ reFourierTest_even h hC ξ)
  have hSum := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi (F.integrable (μ := volume))
  have hFull : (∫ ξ : ℝ, F ξ) = h 0 := reFourierTest_integral h
  rw [compl_Ioi, hE, hFull] at hSum
  change (∫ ξ in Ioi (0:ℝ), F ξ) = h 0 / 2
  linarith

private noncomputable def zeroWeight (z : PositiveZero) : ℝ :=
  (Zeta23.zeroMult z.val : ℝ) / (1+z.val.im^2)

private lemma zeroWeight_nonneg (z : PositiveZero) : 0 ≤ zeroWeight z := by
  unfold zeroWeight
  positivity

private lemma summable_zeroWeight : Summable zeroWeight := by
  let e (z : PositiveZero) : MasulloRH.ZetaZerosInTraceStrip (1/2) :=
    ⟨z.val, z.prop.1.1, z.prop.1.2.1, z.prop.1.2.2,
      abs_lt.mpr ⟨by linarith [z.prop.1.2.1], by linarith [z.prop.1.2.2]⟩⟩
  have he : Function.Injective e := by
    intro x y he
    exact Subtype.ext (congrArg (fun u : MasulloRH.ZetaZerosInTraceStrip (1/2) ↦ u.val) he)
  have hs := (MasulloRH.weighted_zero_summability (1/2) (by norm_num)).comp_injective he
  exact hs

private lemma inverse_scale_weight {ε y : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ε^2/(1+(ε*y/(2*Real.pi))^2) ≤ (2*Real.pi)^2/(1+y^2) := by
  let c := 2*Real.pi
  have hc : 1 ≤ c := by dsimp [c]; linarith [Real.pi_gt_three]
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  change ε^2/(1+(ε*y/c)^2) ≤ c^2/(1+y^2)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ = ε^2 + ε^2*y^2 := by ring
    _ ≤ c^2 + ε^2*y^2 := add_le_add (pow_le_pow_left₀ hε.le (hε₁.trans hc) 2) le_rfl
    _ = _ := by field_simp [hc0.ne']


private noncomputable def realShrinkingMellin (h : 𝓢(ℝ, ℝ)) (ε : ℝ) (z : ℂ) : ℝ :=
  (shrinkingMellin (complexSchwartzTest h) ε z).re

private noncomputable def spectralMellinError (h : 𝓢(ℝ, ℝ)) (ε : ℝ) (z : PositiveZero) : ℝ :=
  (Zeta23.zeroMult z.val : ℝ) *
    (realShrinkingMellin h ε z.val - reFourierTest h (ε*z.val.im/(2*Real.pi)))

private lemma uniform_spectralMellinError (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    ∃ ε₀ > (0:ℝ), ε₀ ≤ 1 ∧ ∃ D ≥ (0:ℝ),
      (∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ z : PositiveZero,
        ‖(2*ε)*spectralMellinError h ε z‖ ≤ D*zeroWeight z) ∧
      Tendsto (fun ε : ℝ ↦ ∑' z : PositiveZero, (2*ε)*spectralMellinError h ε z)
        (𝓝[>] 0) (𝓝 0) := by
  let f := complexSchwartzTest h
  obtain ⟨ε₀,hε₀,hε₀₁,C,hC0,hErr⟩ := shrinkingMellin_uniform_strip_error f
    (hasCompactSupport_complexSchwartzTest h hC)
  let c := 2*Real.pi
  let D := 2*C*c^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hLocal (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ ε₀) (z : PositiveZero) :
      ‖(2*ε)*spectralMellinError h ε z‖ ≤
      2*C*(Zeta23.zeroMult z.val : ℝ)*(ε^2/(1+(ε*z.val.im/c)^2)) := by
    let u := ε*z.val.im/c
    let m : ℝ := Zeta23.zeroMult z.val
    have hRe :
        |realShrinkingMellin h ε z.val - reFourierTest h u| ≤
          C*ε/(1+u^2) := by
      rw [← reFourierTest_even h hC u, reFourierTest_apply, realShrinkingMellin, ← Complex.sub_re]
      refine (Complex.abs_re_le_norm _).trans ?_
      have he : -u = -ε*z.val.im/(2*Real.pi) := by unfold u c; ring
      rw [he]
      exact hErr ε hε hε' z.val z.prop.1.2.1.le z.prop.1.2.2.le
    change ‖(2*ε)*(m*(realShrinkingMellin h ε z.val - reFourierTest h u))‖ ≤ _
    have hm : 0 ≤ m := Nat.cast_nonneg _
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ)),
      abs_of_pos hε, abs_of_nonneg hm]
    calc
      _ ≤ (2*ε)*(m*(C*ε/(1+u^2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRe hm) (by positivity)
      _ = _ := by dsimp only [m, u]; ring
  have hDom (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ ε₀) (z : PositiveZero) :
      ‖(2*ε)*spectralMellinError h ε z‖ ≤ D*zeroWeight z := by
    calc
      _ ≤ 2*C*(Zeta23.zeroMult z.val : ℝ)*(ε^2/(1+(ε*z.val.im/c)^2)) :=
        hLocal ε hε hε' z
      _ ≤ 2*C*(Zeta23.zeroMult z.val : ℝ)*(c^2/(1+z.val.im^2)) :=
        mul_le_mul_of_nonneg_left (inverse_scale_weight hε (hε'.trans hε₀₁)) (by positivity)
      _ = _ := by unfold D zeroWeight; ring
  refine ⟨ε₀,hε₀,hε₀₁,D,hD,hDom,?_⟩
  have hSmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < ε₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hε₀)
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ ε₀ := by
    filter_upwards [self_mem_nhdsWithin, hSmall] with ε hε hε' 
    exact ⟨hε, le_of_lt hε'⟩
  have hPoint (z : PositiveZero) :
      Tendsto (fun ε : ℝ ↦ (2*ε)*spectralMellinError h ε z) (𝓝[>] 0) (𝓝 0) := by
    let m : ℝ := Zeta23.zeroMult z.val
    have hC' : Continuous (fun ε : ℝ ↦ 2*C*m*ε^2) := by fun_prop
    have hlim : Tendsto (fun ε : ℝ ↦ 2*C*m*ε^2) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hC'.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hevent] with ε he
    refine (hLocal ε he.1 he.2 z).trans ?_
    exact mul_le_mul_of_nonneg_left (div_le_self (sq_nonneg ε) (le_add_of_nonneg_right (sq_nonneg _))) (by positivity)
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
    (f := fun ε : ℝ ↦ fun z : PositiveZero ↦ (2*ε)*spectralMellinError h ε z)
    (g := fun _ : PositiveZero ↦ (0:ℝ))
    (summable_zeroWeight.mul_left D)
    hPoint (hevent.mono (fun ε he z ↦ hDom ε he.1 he.2 z))

private lemma scaledMellinError_summable
    (h : 𝓢(ℝ, ℝ)) {ε D : ℝ} (hε : 0 < ε)
    (hD : ∀ z : PositiveZero, ‖(2*ε)*spectralMellinError h ε z‖ ≤ D*zeroWeight z) :
    Summable (spectralMellinError h ε) := by
  have hs : Summable (fun z ↦ (2*ε)*spectralMellinError h ε z) :=
    (summable_zeroWeight.mul_left D).of_norm_bounded hD
  refine (hs.mul_left (2*ε)⁻¹).congr (fun z ↦ ?_)
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : 2*ε ≠ 0), one_mul]

/-- The positive-half Mellin spectral sum, counted with full multiplicities and reflected
by complex conjugation, has the same leading logarithm as the critical-line weights. -/
theorem shrinking_compact_test_mellin_zero_scaling_aux (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    ∃ ε₀ > (0:ℝ), ∃ C ≥ (0:ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      Summable (fun z : PositiveZero ↦ (Zeta23.zeroMult z.val : ℝ)*realShrinkingMellin h ε z.val) ∧
      |2*ε*(∑' z : PositiveZero, (Zeta23.zeroMult z.val : ℝ)*realShrinkingMellin h ε z.val) -
        h 0*Real.log ε⁻¹| ≤ C := by
  obtain ⟨ε₀,hε₀,hε₀₁,D,hD,hErr,_⟩ := uniform_spectralMellinError h hC
  let c := 2*Real.pi
  have hc : 1 ≤ c := by dsimp [c]; linarith [Real.pi_gt_three]
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  let F := reFourierTest h
  obtain ⟨B,hB,hBound⟩ := MasulloRH.weighted_positive_zeta_zeros_schwartz_scaling F
  have hj : (∑' z : PositiveZero, zeroWeight z) ≥ 0 := tsum_nonneg zeroWeight_nonneg
  let A := D*(∑' z : PositiveZero, zeroWeight z)
  let M := |h 0*Real.log c|
  refine ⟨ε₀,hε₀,A+2*c*B+M,by dsimp [A,M]; positivity,?_⟩
  intro ε hε hε'
  let δ := ε/c
  have hδ : 0 < δ := div_pos hε hc0
  have hδ₁ : δ ≤ 1 := (div_le_one₀ hc0).mpr ((hε'.trans hε₀₁).trans hc)
  let w (z : PositiveZero) := (Zeta23.zeroMult z.val : ℝ)*F (δ*z.val.im)
  let v (z : PositiveZero) := (Zeta23.zeroMult z.val : ℝ)*realShrinkingMellin h ε z.val
  obtain ⟨hw,hBW⟩ := hBound δ hδ hδ₁
  have hw' : Summable w := hw
  have hP (z : PositiveZero) : spectralMellinError h ε z = v z - w z := by
    unfold w v spectralMellinError δ c F
    rw [show ε/(2*Real.pi)*z.val.im = ε*z.val.im/(2*Real.pi) by ring]
    ring
  have hE := scaledMellinError_summable h hε (hErr ε hε hε')
  have hv : Summable v := (hE.add hw').congr (fun z ↦ by rw [hP]; ring)
  refine ⟨hv, ?_⟩
  have hEs : Summable (fun z : PositiveZero ↦ (2*ε)*spectralMellinError h ε z) :=
    hE.mul_left (2*ε)
  have hA : |(2*ε)*(∑' z : PositiveZero, v z) - (2*ε)*(∑' z : PositiveZero, w z)| ≤ A := by
    rw [← mul_sub, ← hv.tsum_sub hw', ← tsum_mul_left]
    change ‖(∑' z : PositiveZero, (2*ε)*(v z-w z))‖ ≤ A
    simp only [← hP]
    have hb := (hEs.norm.tsum_le_tsum (hErr ε hε hε') (summable_zeroWeight.mul_left D))
    exact (norm_tsum_le_tsum_norm hEs.norm).trans (by simpa only [tsum_mul_left, A] using hb)
  have hF : (∫ u in Ioi (0:ℝ), F u) = h 0/2 := integral_positive_reFourierTest h hC
  have hB' : |(2*ε)*(∑' z : PositiveZero, w z) - h 0*Real.log δ⁻¹| ≤ 2*c*B := by
    change |δ*(∑' z : PositiveZero, w z) - (1/c)*Real.log δ⁻¹*(∫ u in Ioi (0:ℝ),F u)| ≤ B at hBW
    rw [hF] at hBW
    have hX : (2*ε)*(∑' z : PositiveZero, w z) - h 0*Real.log δ⁻¹ =
        (2*c)*(δ*(∑' z : PositiveZero, w z) - (1/c)*Real.log δ⁻¹*(h 0/2)) := by
      unfold δ
      field_simp [hc0.ne']
    rw [hX, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*c)]
    exact mul_le_mul_of_nonneg_left hBW (by positivity)
  have hL : Real.log δ⁻¹ = Real.log ε⁻¹ + Real.log c := by
    unfold δ
    rw [Real.log_inv, Real.log_div hε.ne' hc0.ne', Real.log_inv]
    ring
  have hEq :
      (2*ε)*(∑' z : PositiveZero, v z) - h 0*Real.log ε⁻¹ =
        ((2*ε)*(∑' z : PositiveZero, v z)-(2*ε)*(∑' z : PositiveZero, w z)) +
        ((2*ε)*(∑' z : PositiveZero, w z)-h 0*Real.log δ⁻¹) + h 0*Real.log c := by
    rw [hL]
    ring
  change |(2*ε)*(∑' z : PositiveZero, v z) - h 0*Real.log ε⁻¹| ≤ _
  rw [hEq]
  refine (abs_add_le _ _).trans ?_
  exact add_le_add ((abs_add_le _ _).trans (add_le_add hA hB')) le_rfl

/-- The strip tilt changes the shrinking positive-half spectral sum by a quantity
that tends to zero after multiplication by the shrinking scale. -/
theorem scaled_mellin_tilt_sum_tendsto_zero (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    Tendsto (fun ε : ℝ ↦ ∑' z : PositiveZero,
      (2*ε)*((Zeta23.zeroMult z.val : ℝ) *
        (realShrinkingMellin h ε z.val - reFourierTest h (ε*z.val.im/(2*Real.pi)))))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨_,_,_,_,_,_,hLim⟩ := uniform_spectralMellinError h hC
  exact hLim


end MasulloAudit

open MeasureTheory

theorem solution (h : SchwartzMap ℝ ℝ) (hC : HasCompactSupport h) :
    let M := fun (ε : ℝ) (z : ℂ) ↦
      (∫ x : ℝ, Complex.exp ((ε : ℂ)*(z-1/2)*(x:ℂ)) * (h x : ℂ)).re
    let F := fun u : ℝ ↦
      (FourierTransform.fourier (fun x : ℝ ↦ (h x : ℂ)) u).re
    (∃ ε₀ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      Summable (fun z : {z : ℂ // Zeta23.IsNontrivialZero z ∧ 0 < z.im} ↦
        (Zeta23.zeroMult z.val : ℝ) * M ε z.val) ∧
      |2*ε*(∑' z : {z : ℂ // Zeta23.IsNontrivialZero z ∧ 0 < z.im},
          (Zeta23.zeroMult z.val : ℝ) * M ε z.val) - h 0 * Real.log ε⁻¹| ≤ C) ∧
    Filter.Tendsto
      (fun ε : ℝ ↦ ∑' z : {z : ℂ // Zeta23.IsNontrivialZero z ∧ 0 < z.im},
        (2*ε)*((Zeta23.zeroMult z.val : ℝ) *
          (M ε z.val - F (ε*z.val.im/(2*Real.pi)))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
  exact ⟨MasulloAudit.shrinking_compact_test_mellin_zero_scaling_aux h hC,
    MasulloAudit.scaled_mellin_tilt_sum_tendsto_zero h hC⟩
