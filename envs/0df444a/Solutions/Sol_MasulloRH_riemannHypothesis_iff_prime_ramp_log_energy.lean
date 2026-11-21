-- Prove2me | solution 1 for MasulloRH.riemannHypothesis_iff_prime_ramp_log_energy
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:25:11.051222+00:00
-- url     : https://prove2.me/submissions/f7477af0-50be-4647-ad4c-6a74edcb4b91

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_finite_ordinate_prime_ramp_approximation
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib
open Filter Finset Set Topology MeasureTheory ArithmeticFunction
open scoped Interval
noncomputable section
open MasulloRH
namespace RampEnergyProof
private abbrev Z := ZetaZerosInTraceStrip (1/2)
private def G (x : ℝ) : ℝ := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
    x*(Real.log x-1-Real.eulerMascheroniConstant)
private theorem small_G {x : ℝ} (hx : 1≤x) (h2 : x<2) : |G x|≤6 := by
  have hfl : ⌊x⌋₊=1 := Nat.floor_eq_iff (by linarith : 0≤x) |>.mpr ⟨by simpa,by norm_num; exact h2⟩
  have hG : G x = -x*(Real.log x-1-Real.eulerMascheroniConstant) := by simp [G,hfl,Finset.sum_range_succ]
  rw [hG,abs_mul,abs_neg,abs_of_nonneg (by linarith : 0≤x)]
  have hl := Real.log_nonneg hx
  have hl' := Real.log_le_log (by linarith : 0<x) h2.le
  have hcoef : |Real.log x-1-Real.eulerMascheroniConstant|≤3 := abs_le.mpr ⟨by linarith [Real.eulerMascheroniConstant_lt_two_thirds],by linarith [Real.log_two_lt_d9,Real.one_half_lt_eulerMascheroniConstant]⟩
  linarith [mul_le_mul_of_nonneg_left hcoef (by linarith : 0≤x)]

private theorem ratio_bounded : ∃ M : ℝ, 0≤M ∧ ∀ x : ℝ, 1≤x → |G x/x|≤M := by
  refine ⟨9,by norm_num,fun x hx => ?_⟩
  have hx0 : 0<x := by linarith
  rw [abs_div,abs_of_pos hx0,div_le_iff₀ hx0]
  by_cases h2 : 2≤x
  · have h := finite_ordinate_prime_ramp_approximation.2.2.2 x h2
    change |G x|≤9*x^(0.8749570698:ℝ) at h
    have he := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (0.8749570698:ℝ)≤1)
    rw [Real.rpow_one] at he
    linarith
  · linarith [small_G hx (lt_of_not_ge h2)]

/- The ramp transform and its pole subtraction follow the verified submission 2850659b by masullo-night. The absolute convergence in the full half-plane Re s > 1 uses the von Mangoldt Dirichlet series, and the boundary normalization below is new. -/
open Real Complex Metric
noncomputable def gammaMoment (a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  u^n * Real.exp (-(a*u)) / (n.factorial : ℝ)

theorem gammaMoment_nonneg (a : ℝ) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ gammaMoment a n u := by
  unfold gammaMoment
  positivity

theorem gammaMoment_integrable {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntegrableOn (gammaMoment a n) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) zero_lt_one ha
  unfold gammaMoment
  simpa only [IntegrableOn, Real.rpow_one, Real.rpow_natCast, neg_mul] using
    h.div_const (n.factorial : ℝ)
private noncomputable def weightedIntegrand (g : ℝ → ℝ) (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (g u : ℂ) * (u:ℂ)^n * Complex.exp (-s*(u:ℂ))

private noncomputable def weightedLaplace (g : ℝ → ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Ioi (0:ℝ), weightedIntegrand g n s u

private theorem weightedIntegrand_measurable {g : ℝ → ℝ} (hg : Measurable g) (n : ℕ) (s : ℂ) :
    Measurable (weightedIntegrand g n s) := by
  unfold weightedIntegrand
  fun_prop

private theorem weightedIntegrand_bound {g : ℝ → ℝ} {K B b : ℝ}
    (hK : 0 ≤ K) (hg : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B+b ≤ s.re) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ‖weightedIntegrand g n s u‖ ≤ ((n.factorial:ℝ)*K)*gammaMoment b n u := by
  have hfact : 0 < (n.factorial:ℝ) := by exact_mod_cast n.factorial_pos
  have he : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  unfold weightedIntegrand
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_of_nonneg hu, Complex.norm_exp, he]
  have hG : |g u| * ((u^n)*Real.exp (-s.re*u)) ≤
      (K*Real.exp (B*u))*((u^n)*Real.exp (-s.re*u)) :=
    mul_le_mul_of_nonneg_right (hg u hu) (by positivity)
  have hshift : Real.exp (B*u) * Real.exp (-s.re*u) = Real.exp (-((s.re-B)*u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he' : Real.exp (-((s.re-B)*u)) ≤ Real.exp (-(b*u)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (by linarith) hu))
  calc
    _ = |g u| * ((u^n)*Real.exp (-s.re*u)) := by ring
    _ ≤ (K*Real.exp (B*u))*((u^n)*Real.exp (-s.re*u)) := hG
    _ = K*(u^n)*(Real.exp (B*u)*Real.exp (-s.re*u)) := by ring
    _ ≤ K*(u^n)*Real.exp (-(b*u)) := by rw [hshift]; exact mul_le_mul_of_nonneg_left he' (by positivity)
    _ = _ := by unfold gammaMoment; field_simp [hfact.ne']

private theorem integrable_weightedIntegrand {g : ℝ → ℝ} (hg : Measurable g) {K B b : ℝ}
    (hK : 0 ≤ K) (hb : 0 < b) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B+b ≤ s.re) (n : ℕ) :
    IntegrableOn (weightedIntegrand g n s) (Ioi 0) := by
  refine ((gammaMoment_integrable hb n).const_mul ((n.factorial:ℝ)*K)).mono'
    (weightedIntegrand_measurable hg n s).aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun u hu => weightedIntegrand_bound hK hgK hs n hu.le)

private theorem hasDerivAt_weightedLaplace {g : ℝ → ℝ} (hg : Measurable g) {K B : ℝ}
    (hK : 0 ≤ K) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B < s.re) (n : ℕ) :
    HasDerivAt (weightedLaplace g n) (-weightedLaplace g (n+1) s) s := by
  let b := (s.re-B)/2
  have hb : 0 < b := by dsimp [b]; linarith
  have hz (z : ℂ) (hz : z ∈ ball s b) : B+b ≤ z.re := by
    have hd : ‖z-s‖ < b := by simpa only [mem_ball, dist_eq_norm] using hz
    have hr := (abs_lt.mp ((Complex.abs_re_le_norm (z-s)).trans_lt hd)).1
    simp only [Complex.sub_re] at hr
    dsimp [b] at hr ⊢
    linarith
  have hbnd : ∀ᵐ u ∂(volume : Measure ℝ).restrict (Ioi 0), ∀ z ∈ ball s b,
      ‖-weightedIntegrand g (n+1) z u‖ ≤ (((n+1).factorial:ℝ)*K)*gammaMoment b (n+1) u :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu z hzs => by
      rw [norm_neg]
      exact weightedIntegrand_bound hK hgK (hz z hzs) (n+1) hu.le)
  have hder (u : ℝ) (z : ℂ) :
      HasDerivAt (fun w => weightedIntegrand g n w u) (-weightedIntegrand g (n+1) z u) z := by
    have he : HasDerivAt (fun w : ℂ => -w*(u:ℂ)) (-(u:ℂ)) z := by
      simpa using (hasDerivAt_id z).neg.mul_const (u:ℂ)
    refine (he.cexp.const_mul ((g u : ℂ)*(u:ℂ)^n)).congr_deriv ?_
    unfold weightedIntegrand
    rw [pow_succ]
    ring
  have hi := (gammaMoment_integrable hb (n+1)).const_mul (((n+1).factorial:ℝ)*K)
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := weightedIntegrand g n) (F' := fun z u => -weightedIntegrand g (n+1) z u)
    (ball_mem_nhds s hb)
    (Eventually.of_forall fun z => (weightedIntegrand_measurable hg n z).aestronglyMeasurable)
    (integrable_weightedIntegrand hg hK hb hgK (hz s (mem_ball_self hb)) n)
    ((weightedIntegrand_measurable hg (n+1) s).neg.aestronglyMeasurable)
    hbnd hi (Eventually.of_forall fun u z _ => hder u z)).2
  unfold weightedLaplace
  rw [← integral_neg]
  exact hh
theorem laplace_integrable_of_exponential_bound {g : ℝ → ℝ} (hg : Measurable g)
    {K B : ℝ} (hK : 0 ≤ K) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B < s.re) :
    IntegrableOn (fun u : ℝ => (g u:ℂ)*Complex.exp (-s*(u:ℂ))) (Ioi 0) := by
  have hb : 0 < s.re-B := sub_pos.mpr hs
  have hσ : B+(s.re-B) ≤ s.re := by linarith
  have h := integrable_weightedIntegrand hg hK hb hgK hσ 0
  have he : weightedIntegrand g 0 s = (fun u : ℝ => (g u:ℂ)*Complex.exp (-s*(u:ℂ))) := by
    funext u
    simp [weightedIntegrand]
  rwa [he] at h

theorem linear_exponential_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => (u:ℂ)*Complex.exp (-s*(u:ℂ))) (Ioi 0) := by
  have h := integrable_weightedIntegrand
    (g := fun _ => (1:ℝ)) measurable_const (K := 1) (B := 0) zero_le_one hs
      (fun u _ => by simp) (s := s) (by simp : (0:ℝ)+s.re ≤ s.re) 1
  have he : weightedIntegrand (fun _ => 1) 1 s =
      (fun u : ℝ => (u:ℂ)*Complex.exp (-s*(u:ℂ))) := by
    funext u
    simp [weightedIntegrand]
  rwa [he] at h

/-- The first moment of a complex exponential with positive decay. -/
theorem linear_exponential_integral {s : ℂ} (hs : 0 < s.re) :
    (∫ u in Ioi (0:ℝ), (u:ℂ)*Complex.exp (-s*(u:ℂ))) = 1/s^2 := by
  have he (z : ℂ) (hz : 0 < z.re) :
      weightedLaplace (fun _ => 1) 0 z = z⁻¹ := by
    have h := integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
    simpa [weightedLaplace, weightedIntegrand, div_eq_mul_inv] using h
  have hnear : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have hlocal : weightedLaplace (fun _ => 1) 0 =ᶠ[𝓝 s] (fun z : ℂ => z⁻¹) :=
    hnear.mono he
  have hd : HasDerivAt (weightedLaplace (fun _ => 1) 0) (-weightedLaplace (fun _ => 1) 1 s) s :=
    hasDerivAt_weightedLaplace measurable_const (K := 1) (B := 0) zero_le_one
      (fun u _ => by simp) hs 0
  have hz : s ≠ 0 := ne_zero_of_re_pos hs
  have hInv := hasDerivAt_inv (x := s) hz
  have ht := hd.deriv.symm.trans (hlocal.deriv_eq.trans hInv.deriv)
  simpa [weightedLaplace, weightedIntegrand, div_eq_mul_inv] using neg_injective ht

private theorem analyticAt_dslope_of_analyticAt {f : ℂ → ℂ} {z : ℂ}
    (h : AnalyticAt ℂ f z) : AnalyticAt ℂ (dslope f z) z := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

private noncomputable def zetaWindowNumerator (s : ℂ) : ℂ :=
  (1 + (Real.eulerMascheroniConstant:ℂ))*s - 1 - deriv riemannZeta₁ s / riemannZeta₁ s

/-- The regularized transform of the Riemann-zeta ramp error, with
the singularity at one removed. -/
noncomputable def zetaWindowTransform (s : ℂ) : ℂ :=
  dslope zetaWindowNumerator 1 s / s

private theorem zetaWindowNumerator_one : zetaWindowNumerator 1 = 0 := by
  simp [zetaWindowNumerator]

private theorem zetaWindowNumerator_analytic {s : ℂ} (h : riemannZeta₁ s ≠ 0) :
    AnalyticAt ℂ zetaWindowNumerator s := by
  have ha : AnalyticAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁.analyticAt _
  unfold zetaWindowNumerator
  exact ((analyticAt_const.mul analyticAt_id).sub analyticAt_const).sub (ha.deriv.div ha h)

private theorem zeta₁_eq_product {s : ℂ} (h : s ≠ 1) :
    riemannZeta₁ s = (s-1)*riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul h, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr h), one_mul]

private theorem zetaWindowTransform_eq_quotient {s : ℂ} (h : s ≠ 1) :
    zetaWindowTransform s = zetaWindowNumerator s / (s*(s-1)) := by
  rw [zetaWindowTransform, dslope_of_ne _ h, slope_def_field,
    zetaWindowNumerator_one, sub_zero, div_div, mul_comm (s-1)]

theorem zetaWindowTransform_differentiableAt {s : ℂ} (hs : 0 < s.re)
    (hζ : riemannZeta s ≠ 0) : DifferentiableAt ℂ zetaWindowTransform s := by
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos hs
  have hnum : DifferentiableAt ℂ (dslope zetaWindowNumerator 1) s := by
    rcases eq_or_ne s 1 with rfl | h
    · exact (analyticAt_dslope_of_analyticAt
        (zetaWindowNumerator_analytic (by simp))).differentiableAt
    · refine (differentiableAt_dslope_of_ne h).mpr (zetaWindowNumerator_analytic ?_).differentiableAt
      rw [zeta₁_eq_product h]
      exact mul_ne_zero (sub_ne_zero.mpr h) hζ
  unfold zetaWindowTransform
  exact hnum.div differentiableAt_id hs₀

/-- Away from its poles this is the usual Mellin transform expression. -/
theorem zetaWindowTransform_eq_logDerivative {s : ℂ} (hs : 1 < s.re) :
    zetaWindowTransform s =
      -(deriv riemannZeta s / riemannZeta s)/(s*(s-1)) -
      1/(s-1)^2 + (1+(Real.eulerMascheroniConstant:ℂ))/(s-1) := by
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hs₁ : s ≠ 1 := by intro h; simp [h] at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hloc : ∀ᶠ z : ℂ in 𝓝 s, z ≠ 1 := isOpen_ne.mem_nhds hs₁
  have he : riemannZeta₁ =ᶠ[𝓝 s] fun z => (z-1)*riemannZeta z :=
    hloc.mono (fun _ h => zeta₁_eq_product h)
  have hd : deriv riemannZeta₁ s = riemannZeta s + (s-1)*deriv riemannZeta s := by
    rw [he.deriv_eq]
    have hD : DifferentiableAt ℂ (fun z => z-(1:ℂ)) s := differentiableAt_id.sub_const _
    rw [deriv_fun_mul hD (differentiableAt_riemannZeta hs₁)]
    have heq : deriv (fun z => z-(1:ℂ)) s = 1 := by simpa using ((hasDerivAt_id s).sub_const (1:ℂ)).deriv
    rw [heq, one_mul]
  rw [zetaWindowTransform_eq_quotient hs₁, zetaWindowNumerator, zeta₁_eq_product hs₁, hd]
  field_simp [hs₀, sub_ne_zero.mpr hs₁, hz]
  ring
private noncomputable def rampWeight (n : ℕ) (x : ℝ) : ℝ := max (x/(n:ℝ)-1) 0

/-- The corrected, ramp-smoothed von Mangoldt sum at modulus one. -/
noncomputable def zetaRampError (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (⌊x⌋₊+1), vonMangoldt n * rampWeight n x) -
    x*(Real.log x-1-Real.eulerMascheroniConstant)

private theorem rampWeight_zero_off_range {n : ℕ} {x : ℝ} (h : n ∉ Finset.range (⌊x⌋₊+1)) :
    rampWeight n x = 0 := by
  have hn : ⌊x⌋₊+1 ≤ n := by simpa using h
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx : x ≤ (n:ℝ) := (Nat.lt_floor_add_one x).le.trans (by exact_mod_cast hn)
  unfold rampWeight
  exact max_eq_right (sub_nonpos.mpr ((div_le_one hn₀).mpr hx))

private theorem zetaRamp_sum_eq_tsum (x : ℝ) :
    (∑ n ∈ Finset.range (⌊x⌋₊+1), vonMangoldt n * rampWeight n x) =
      ∑' n : ℕ, vonMangoldt n * rampWeight n x := by
  symm
  exact tsum_eq_sum (fun n hn => by rw [rampWeight_zero_off_range hn, mul_zero])

theorem zetaRampError_measurable : Measurable zetaRampError := by
  unfold zetaRampError
  simp_rw [zetaRamp_sum_eq_tsum]
  apply Measurable.sub
  · apply Measurable.tsum
    intro n
    unfold rampWeight
    fun_prop
  · have hl := Real.measurable_log
    fun_prop

private noncomputable def rampLaplaceTerm (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (rampWeight n (Real.exp u) : ℂ) * Complex.exp (-s*(u:ℂ))

private theorem rampLaplaceTerm_zero (s : ℂ) : rampLaplaceTerm 0 s = 0 := by
  funext u
  simp [rampLaplaceTerm, rampWeight]

private theorem rampLaplaceTerm_integrable {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    IntegrableOn (rampLaplaceTerm n s) (Ioi 0) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [rampLaplaceTerm_zero]
    exact integrable_zero ℝ ℂ ((volume : Measure ℝ).restrict (Ioi 0))
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hdec : 1-s.re < 0 := by linarith
  have hi := (integrableOn_exp_mul_Ioi hdec 0).const_mul ((n:ℝ)⁻¹)
  have hmeas : Measurable (rampLaplaceTerm n s) := by unfold rampLaplaceTerm rampWeight; fun_prop
  refine hi.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  have he : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  have hle : rampWeight n (Real.exp u) ≤ Real.exp u/(n:ℝ) :=
    max_le (by linarith) (by positivity)
  have hh : 0 ≤ rampWeight n (Real.exp u) := le_max_right _ _
  change ‖rampLaplaceTerm n s u‖ ≤ (n:ℝ)⁻¹*Real.exp ((1-s.re)*u)
  rw [rampLaplaceTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh, Complex.norm_exp, he]
  calc
    _ ≤ (Real.exp u/(n:ℝ)) * Real.exp (-s.re*u) :=
      mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
    _ = (n:ℝ)⁻¹*(Real.exp u*Real.exp (-s.re*u)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem rampLaplaceTerm_integral {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (0:ℝ), rampLaplaceTerm n s u) = (n:ℂ)^(-s)/(s*(s-1)) := by
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn₁ : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let l := Real.log (n:ℝ)
  have hl : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hn)
  have hr : (-(s-1)).re < 0 := by simp [Complex.sub_re]; linarith
  have hr' : (-s).re < 0 := by simp; linarith
  let F (u : ℝ) := (n:ℂ)⁻¹*Complex.exp (-(s-1)*(u:ℂ))-Complex.exp (-s*(u:ℂ))
  have he : rampLaplaceTerm n s = (Ioi l).indicator F := by
    funext u
    by_cases hu : u ∈ Ioi l
    · have hx : (n:ℝ) < Real.exp u := by
        simpa [l, Real.exp_log hn₀] using Real.exp_lt_exp.mpr hu
      have hw : 0 ≤ Real.exp u/(n:ℝ)-1 := sub_nonneg.mpr ((one_le_div hn₀).mpr hx.le)
      rw [indicator_of_mem hu, rampLaplaceTerm, rampWeight, max_eq_left hw]
      push_cast
      have h : Complex.exp (-(s-1)*(u:ℂ)) = Complex.exp (u:ℂ)*Complex.exp (-s*(u:ℂ)) := by
        rw [← Complex.exp_add]; congr 1; ring
      dsimp [F]
      rw [h]
      ring
    · have hx : Real.exp u ≤ (n:ℝ) := by
        have h : u ≤ l := le_of_not_gt hu
        simpa [l, Real.exp_log hn₀] using Real.exp_le_exp.mpr h
      rw [indicator_of_notMem hu, rampLaplaceTerm, rampWeight,
        max_eq_right (sub_nonpos.mpr ((div_le_one hn₀).mpr hx)), Complex.ofReal_zero, zero_mul]
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hs₁ : s-1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  rw [he, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hl)]
  dsimp [F]
  rw [integral_sub ((integrableOn_exp_mul_complex_Ioi hr l).const_mul _)
    (integrableOn_exp_mul_complex_Ioi hr' l), integral_const_mul,
    integral_exp_mul_complex_Ioi hr, integral_exp_mul_complex_Ioi hr']
  have hcp : Complex.exp (-s*(l:ℂ)) = (n:ℂ)^(-s) := by
    rw [Complex.cpow_def_of_ne_zero hn₁, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn₀.le]
    dsimp [l]
    rw [mul_comm]
  have hex : Complex.exp (-(s-1)*(l:ℂ)) = Complex.exp (-s*(l:ℂ))*(n:ℂ) := by
    rw [show -(s-1)*(l:ℂ) = -s*(l:ℂ)+(l:ℂ) by ring, Complex.exp_add,
      ← Complex.ofReal_exp, show Real.exp l = (n:ℝ) by exact Real.exp_log hn₀,
      Complex.ofReal_natCast]
  rw [hex,hcp]
  field_simp [hs₀,hs₁,hn₁]
  ring

private theorem norm_rampLaplaceTerm_eq_real_cast (n : ℕ) (s : ℂ) (u : ℝ) :
    (‖rampLaplaceTerm n s u‖:ℂ) = rampLaplaceTerm n ((s.re:ℝ):ℂ) u := by
  have hre : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  have h : 0 ≤ rampWeight n (Real.exp u) := le_max_right _ _
  simp only [rampLaplaceTerm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg h, Complex.norm_exp, hre]
  push_cast
  rfl

private theorem rampLaplaceTerm_integral_norm {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (0:ℝ), ‖rampLaplaceTerm n s u‖) =
      (n:ℝ)^(-s.re)/(s.re*(s.re-1)) := by
  apply Complex.ofReal_injective
  have hnorm : ((∫ u in Ioi (0:ℝ), ‖rampLaplaceTerm n s u‖ : ℝ) : ℂ) =
      ∫ u in Ioi (0:ℝ), rampLaplaceTerm n ((s.re:ℝ):ℂ) u := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => norm_rampLaplaceTerm_eq_real_cast n s u)
  rw [hnorm, rampLaplaceTerm_integral hn (by simpa : 1 < ((s.re:ℝ):ℂ).re)]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

private noncomputable def weightedRampTerm (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (vonMangoldt n : ℂ) * rampLaplaceTerm n s u

private theorem weightedRampTerm_integrable {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    IntegrableOn (weightedRampTerm n s) (Ioi 0) := (rampLaplaceTerm_integrable hs n).const_mul _

private theorem summable_weightedRamp_integral_norm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ u in Ioi (0:ℝ), ‖weightedRampTerm n s u‖) := by
  let D : ℝ := s.re*(s.re-1)
  have hsum : Summable (fun n => ‖LSeries.term (fun k : ℕ => (vonMangoldt k : ℂ)) s n‖/D) :=
    (LSeriesSummable_vonMangoldt hs).norm.div_const D
  apply hsum.congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [weightedRampTerm]
  rw [show (fun u => ‖weightedRampTerm n s u‖) =
        (fun u => vonMangoldt n * ‖rampLaplaceTerm n s u‖) by
      funext u
      rw [weightedRampTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg] ]
  rw [integral_const_mul,rampLaplaceTerm_integral_norm (Nat.pos_of_ne_zero hn) hs,LSeries.norm_term_eq,if_neg hn,
    Complex.norm_real,Real.norm_of_nonneg vonMangoldt_nonneg,Real.rpow_neg (Nat.cast_nonneg n)]
  dsimp [D]; ring

private theorem weightedRampTerm_integral {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    (∫ u in Ioi (0:ℝ), weightedRampTerm n s u) =
      LSeries.term (fun k => (vonMangoldt k:ℂ)) s n/(s*(s-1)) := by
  by_cases hn : n = 0
  · simp [hn, weightedRampTerm]
  · unfold weightedRampTerm
    rw [integral_const_mul, rampLaplaceTerm_integral (Nat.pos_of_ne_zero hn) hs,
      LSeries.term_of_ne_zero hn, Complex.cpow_neg]
    ring

private noncomputable def rampArithmeticSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊+1), vonMangoldt n * rampWeight n x

private theorem weightedRampTerm_tsum (s : ℂ) (u : ℝ) :
    (∑' n, weightedRampTerm n s u) =
      (rampArithmeticSum (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ)) := by
  rw [tsum_eq_sum (s := Finset.range (⌊Real.exp u⌋₊+1)) (by
    intro n hn
    rw [weightedRampTerm, rampLaplaceTerm, rampWeight_zero_off_range hn, Complex.ofReal_zero, zero_mul, mul_zero])]
  simp only [weightedRampTerm, rampLaplaceTerm, ← mul_assoc, ← sum_mul, rampArithmeticSum,
    Complex.ofReal_sum, Complex.ofReal_mul]

private theorem rampArithmetic_laplace {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (0:ℝ), (rampArithmeticSum (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))) =
      -(deriv riemannZeta s/riemannZeta s)/(s*(s-1)) := by
  have hσ : 1 < s.re := by linarith
  have hc := hasSum_integral_of_summable_integral_norm
    (fun n => weightedRampTerm_integrable hσ n) (summable_weightedRamp_integral_norm hs)
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun u _ => weightedRampTerm_tsum s u)]
  rw [← hc.tsum_eq]
  simp_rw [weightedRampTerm_integral hσ]
  rw [tsum_div_const]
  change LSeries (fun k => (vonMangoldt k:ℂ)) s/(s*(s-1)) = _
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ]
  rw [neg_div]
private theorem exponential_const_integral {s : ℂ} (hs : 0 < s.re) :
    (∫ u in Ioi (0:ℝ), Complex.exp (-s*(u:ℂ))) = 1/s := by
  have h := integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  simpa [div_eq_mul_inv] using h

private theorem correction_integrable_and_integral {s : ℂ} (hs : 1 < s.re) :
    let F := fun u : ℝ => ((Real.exp u * (u-1-Real.eulerMascheroniConstant) : ℝ):ℂ) *
      Complex.exp (-s*(u:ℂ))
    IntegrableOn F (Ioi (0:ℝ)) ∧
      (∫ u in Ioi (0:ℝ), F u) = 1/(s-1)^2-(1+(Real.eulerMascheroniConstant:ℂ))/(s-1) := by
  let a := s-1
  have ha : 0 < a.re := by simp [a, Complex.sub_re, sub_pos, hs]
  let A (u : ℝ) := (u:ℂ)*Complex.exp (-a*(u:ℂ))
  let B (u : ℝ) := (1+(Real.eulerMascheroniConstant:ℂ))*Complex.exp (-a*(u:ℂ))
  have hF (u : ℝ) :
      ((Real.exp u * (u-1-Real.eulerMascheroniConstant) : ℝ):ℂ)*Complex.exp (-s*(u:ℂ)) =
        A u - B u := by
    dsimp [A,B,a]
    have he : Complex.exp (-(s-1)*(u:ℂ)) = Complex.exp (u:ℂ)*Complex.exp (-s*(u:ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [he]
    push_cast
    ring
  have hA : IntegrableOn A (Ioi 0) := linear_exponential_integrable ha
  have hB : IntegrableOn B (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0).const_mul _
  simp only [hF]
  refine ⟨hA.sub hB,?_⟩
  rw [integral_sub hA hB]
  dsimp [A,B]
  rw [integral_const_mul, linear_exponential_integral ha, exponential_const_integral ha]
  dsimp [a]
  ring
theorem zetaRampError_laplace {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (0:ℝ), (zetaRampError (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))) =
      -(deriv riemannZeta s/riemannZeta s)/(s*(s-1)) -
        1/(s-1)^2 + (1+(Real.eulerMascheroniConstant:ℂ))/(s-1) := by
  obtain ⟨K,hK,hR⟩ := ratio_bounded
  have hG (u : ℝ) (hu : 0≤u) : |zetaRampError (Real.exp u)| ≤ K*Real.exp (1*u) := by
    have h := hR (Real.exp u) (Real.one_le_exp hu)
    rw [abs_div,abs_of_pos (Real.exp_pos u),div_le_iff₀ (Real.exp_pos u)] at h
    simpa only [one_mul,zetaRampError,G,rampWeight] using h
  have hi := laplace_integrable_of_exponential_bound
    (zetaRampError_measurable.comp Real.continuous_exp.measurable) hK hG hs
  let P (u : ℝ) := (rampArithmeticSum (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))
  let Q (u : ℝ) := ((Real.exp u * (u-1-Real.eulerMascheroniConstant) : ℝ):ℂ) *
    Complex.exp (-s*(u:ℂ))
  obtain ⟨hQ,hQi⟩ := correction_integrable_and_integral (by linarith : 1 < s.re)
  have hQi' : (∫ u in Ioi (0:ℝ), Q u) = _ := hQi
  have hQ' : IntegrableOn Q (Ioi (0:ℝ)) := hQ
  have hEq (u : ℝ) : (zetaRampError (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ)) = P u-Q u := by
    simp only [zetaRampError, P, Q, rampArithmeticSum, Real.log_exp]
    push_cast
    ring
  have hi' : IntegrableOn (fun u => P u-Q u) (Ioi (0:ℝ)) := by
    have he : (fun u : ℝ => ((zetaRampError ∘ Real.exp) u:ℂ)*Complex.exp (-s*(u:ℂ))) =
        (fun u => P u-Q u) := funext hEq
    rwa [he] at hi
  have hP : IntegrableOn P (Ioi (0:ℝ)) := by
    have h := hi'.add hQ'
    have he : (fun u => P u-Q u)+Q = P := by
      funext u
      simp
    rwa [he] at h
  have hPi : (∫ u in Ioi (0:ℝ), P u) = -(deriv riemannZeta s/riemannZeta s)/(s*(s-1)) :=
    rampArithmetic_laplace hs
  calc
    _ = ∫ u in Ioi (0:ℝ), P u-Q u := setIntegral_congr_fun measurableSet_Ioi (fun u _ => hEq u)
    _ = _ := by rw [integral_sub hP hQ', hPi, hQi']; ring


private abbrev μ : Measure ℝ := volume.restrict (Ioi (0:ℝ))
private def profile (θ u : ℝ) : ℝ := G (Real.exp u)*Real.exp (-(θ*u))/(1+u)
private theorem measG : Measurable G := zetaRampError_measurable
private theorem measprofile (θ : ℝ) : Measurable (profile θ) := by
  unfold profile; have h := measG; fun_prop
private theorem hxbound {θ : ℝ} (hθ : 0 ≤ θ) (hz : ∀ z : Z, z.val.re ≤ θ) {u : ℝ} (hu : 0 ≤ u) :
    |G (Real.exp u)|  ≤  9*Real.exp (θ*u) := by
  have h1 := Real.one_le_exp hu
  by_cases h2 : 2 ≤ Real.exp u
  · have h := finite_ordinate_prime_ramp_approximation.2.2.1 θ hθ hz (Real.exp u) h2
    change |G (Real.exp u)|  ≤  9*(Real.exp u)^θ at h
    simpa only [←Real.exp_mul,mul_comm u θ] using h
  · have h := small_G h1 (lt_of_not_ge h2)
    linarith [Real.one_le_exp (mul_nonneg hθ hu)]

private def major (u : ℝ) := ((1+u)^2)⁻¹
private theorem major_ible : Integrable major μ := by
  have h := (integrable_inv_one_add_sq.integrableOn (s:=Ioi (0:ℝ)))
  have hm : Measurable major := by unfold major; fun_prop
  apply h.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 0 < u := hu
  rw [Real.norm_of_nonneg (show 0 ≤ major u by unfold major; positivity)]
  unfold major
  exact inv_anti₀ (by positivity) (by nlinarith)

private theorem major_mass : ∫ u in Ioi (0:ℝ),major u = 1 := by
  have hh (u : ℝ) (hu : u∈Ici (0:ℝ)) : HasDerivAt (fun u : ℝ => -(1+u)⁻¹) (major u) u := by
    have hu' : 0 ≤ u := hu
    have hd := (((hasDerivAt_id u).const_add 1).inv (by dsimp; linarith : 1+u ≠ 0)).neg
    exact hd.congr_deriv (by dsimp [major]; ring)
  have hlim : Tendsto (fun u : ℝ => -(1+u)⁻¹) atTop (𝓝 0) := by
    have hc : Tendsto (fun u : ℝ => 1+u) atTop atTop := tendsto_atTop_add_const_left atTop 1 tendsto_id
    simpa only [Function.comp_def,neg_zero] using (tendsto_inv_atTop_zero.comp hc).neg
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' hh major_ible hlim

private theorem profile_bound {θ : ℝ} (hθ : 0 ≤ θ) (hz : ∀ z : Z,z.val.re ≤ θ) {u : ℝ} (hu : 0 ≤ u) :
    (profile θ u)^2  ≤  81*major u := by
  have h := hxbound hθ hz hu
  have hp := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-(θ*u)))
  have he : 9*Real.exp (θ*u)*Real.exp (-(θ*u))=9 := by rw [mul_assoc,←Real.exp_add]; simp
  rw [he] at hp
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ |G (Real.exp u)| * Real.exp (-(θ*u))) hp
  have hn : (G (Real.exp u)*Real.exp (-(θ*u)))^2  ≤  81 := by
    rw [←sq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]; nlinarith only [hs]
  unfold profile major
  rw [div_pow,div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hn (by positivity)

private theorem energy_of_bound {θ : ℝ} (hθ : 0 ≤ θ) (hz : ∀ z : Z,z.val.re ≤ θ) :
    MemLp (profile θ) 2 μ ∧ ∫ u in Ioi (0:ℝ),(profile θ u)^2  ≤  81 := by
  have hpb : ∀ᵐ u ∂μ,(profile θ u)^2  ≤  81*major u :=
    (ae_restrict_mem measurableSet_Ioi).mono fun u hu => profile_bound hθ hz (le_of_lt hu)
  have hm : Measurable (fun u => (profile θ u)^2) := (measprofile θ).pow_const _
  have hi := major_ible.const_mul 81
  have hI : Integrable (fun u => (profile θ u)^2) μ := hi.mono' hm.aestronglyMeasurable
    (hpb.mono fun u hu => by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hu)
  refine ⟨(memLp_two_iff_integrable_sq (measprofile θ).aestronglyMeasurable).mpr hI,?_⟩
  have h := integral_mono_ae hI hi hpb
  simpa only [μ,integral_const_mul,major_mass,mul_one] using h

private def J (s : ℂ) (u : ℝ) : ℂ := (G (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))
private def L (s : ℂ) : ℂ := ∫ u in Ioi (0:ℝ), J s u
private def bump (ε u : ℝ) : ℝ := (1+u)^2*Real.exp (-(ε*u))

private theorem bump_mem {ε : ℝ} (hε : 0 < ε) : MemLp (bump ε) 2 μ := by
  have hpoly (n : ℕ) : MemLp (fun u : ℝ => u^n*Real.exp (-(ε*u))) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    have hi := (gammaMoment_integrable (by linarith : 0 < 2*ε) (2*n)).mul_const (((2*n).factorial):ℝ)
    apply hi.congr
    apply Eventually.of_forall
    intro u
    change gammaMoment (2*ε) (2*n) u * _ = _
    rw [gammaMoment,div_mul_cancel₀ _ (by exact_mod_cast (2*n).factorial_ne_zero)]
    dsimp only
    rw [mul_pow,←Real.exp_nat_mul,←pow_mul]
    norm_num
    ring_nf
  have h := ((hpoly 0).add ((hpoly 1).const_mul 2)).add (hpoly 2)
  apply (memLp_congr_ae _).mp h
  apply Eventually.of_forall
  intro u; dsimp [bump]; ring

private theorem J_meas (s : ℂ) : Measurable (J s) := by
  have h := measG; unfold J; fun_prop
private theorem J_norm {θ ε : ℝ} {s : ℂ} (hs : θ+ε ≤ s.re) {u : ℝ} (hu : 0 ≤ u) :
    ‖J s u‖  ≤  ‖profile θ u‖*((1+u)*Real.exp (-(ε*u))) := by
  have hden : 0 < 1+u := by linarith
  have he (z : ℂ) : (-z*(u:ℂ)).re = -(z.re*u) := by simp [Complex.mul_re]
  simp only [J,profile,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,he,abs_mul,abs_div,
    abs_of_pos (Real.exp_pos _),abs_of_pos hden]
  have hmul := Real.exp_le_exp.mpr (show -(s.re*u)  ≤  -(θ*u)+ -(ε*u) by nlinarith [mul_le_mul_of_nonneg_right hs hu])
  rw [Real.exp_add] at hmul
  apply (mul_le_mul_of_nonneg_left hmul (abs_nonneg _)).trans_eq
  field_simp

private theorem L_diff {θ : ℝ} (hp : MemLp (profile θ) 2 μ) {s : ℂ} (hs : θ < s.re) : DifferentiableAt ℂ L s := by
  let ε := (s.re-θ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let U := {z : ℂ | θ+ε < z.re}
  have hU : U ∈ 𝓝 s := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [ε]; linarith)
  let Bd (u : ℝ) := ‖profile θ u‖*bump ε u
  have hBd : Integrable Bd μ := hp.norm.integrable_mul (bump_mem hε)
  have hder (u : ℝ) (z : ℂ) : HasDerivAt (fun w => J w u) (-(u:ℂ)*J z u) z := by
    have h : HasDerivAt (fun w : ℂ => -w*(u:ℂ)) (-(u:ℂ)) z := by simpa using (hasDerivAt_id z).neg.mul_const (u:ℂ)
    exact (h.cexp.const_mul (G (Real.exp u):ℂ)).congr_deriv (by unfold J; ring)
  have hint : Integrable (J s) μ := by
    apply hBd.mono' (J_meas s).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 ≤ u := le_of_lt hu
    have hj := J_norm (by dsimp [ε]; linarith : θ+ε ≤ s.re) hu'
    exact hj.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by nlinarith : 1+u ≤ (1+u)^2) (Real.exp_nonneg _)) (norm_nonneg _))
  have hdom : ∀ᵐ u : ℝ ∂μ, ∀ z ∈ U, ‖-(u:ℂ)*J z u‖  ≤  Bd u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro z hz
    have hu' := le_of_lt (show 0 < u from hu)
    rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg hu']
    apply (mul_le_mul_of_nonneg_left (J_norm (le_of_lt (show θ+ε < z.re from hz)) hu') hu').trans
    change _  ≤  ‖profile θ u‖*((1+u)^2*Real.exp (-(ε*u)))
    calc _ = ‖profile θ u‖*((u*(1+u))*Real.exp (-(ε*u))) := by ring
         _  ≤  _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_nonneg _)) (norm_nonneg _)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=μ) (F:=J) (F':=fun z u => -(u:ℂ)*J z u) (bound:=Bd) hU
    (Eventually.of_forall fun z => (J_meas z).aestronglyMeasurable) hint
    (show Measurable (fun u : ℝ => -(u:ℂ)*J s u) by have h:=J_meas s; fun_prop).aestronglyMeasurable
    hdom hBd (Eventually.of_forall fun u z _ => hder u z)).2
  exact hd.differentiableAt

private def odeCoeff (s : ℂ) : ℂ := (1+(Real.eulerMascheroniConstant:ℂ))*s-1-s*(s-1)*L s

private theorem initial_ode {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta₁ s = riemannZeta₁ s*odeCoeff s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hZ : riemannZeta₁ s ≠ 0 := by rw [zeta₁_eq_product hs1]; exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_lt_re hs)
  have h : L s = zetaWindowTransform s := (zetaRampError_laplace hs).trans (zetaWindowTransform_eq_logDerivative hs).symm
  rw [zetaWindowTransform_eq_quotient hs1,zetaWindowNumerator] at h
  have he := (eq_div_iff (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))).mp h
  unfold odeCoeff
  field_simp [hZ] at he
  linear_combination he

private theorem bound_of_energy {θ : ℝ} (hθ : θ < 1) (hp : MemLp (profile θ) 2 μ) :
    ∀ z : Z,z.val.re ≤ θ := by
  let D := {s : ℂ | θ < s.re}
  have hopen : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected D := (convex_halfSpace_re_gt θ).isPreconnected
  have hco : AnalyticOnNhd ℂ odeCoeff D := by
    intro s hs
    have hl : AnalyticAt ℂ L s := (DifferentiableOn.analyticAt (s:=D)
      (fun z hz => (L_diff hp hz).differentiableWithinAt) (hopen.mem_nhds hs))
    unfold odeCoeff
    exact ((analyticAt_const.mul analyticAt_id).sub analyticAt_const).sub ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hl)
  have hZ (s : ℂ) : AnalyticAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁.analyticAt s
  have hder : AnalyticOnNhd ℂ (deriv riemannZeta₁) D := fun z _ => (hZ z).deriv
  have hprod : AnalyticOnNhd ℂ (riemannZeta₁*odeCoeff) D := fun z hz => (hZ z).mul (hco z hz)
  have heq : Set.EqOn (deriv riemannZeta₁) (riemannZeta₁*odeCoeff) D :=
    hder.eqOn_of_preconnected_of_eventuallyEq hprod hconn (z₀:=2) (by change θ < (2:ℂ).re; norm_num; linarith)
      (by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re)] with z hz
        exact initial_ode hz)
  intro ρ
  by_contra! hh
  have hρ : ρ.val ∈ D := hh
  have h1 : ρ.val ≠ 1 := fun he => by have := ρ.prop.2.2.1; simp [he] at this
  have hzero : riemannZeta₁ ρ.val = 0 := by rw [zeta₁_eq_product h1,ρ.prop.1,mul_zero]
  have hloc : deriv riemannZeta₁ =ᶠ[𝓝 ρ.val] riemannZeta₁*odeCoeff := by
    filter_upwards [hopen.mem_nhds hρ] with z hz
    exact heq hz
  have hfin : analyticOrderAt riemannZeta₁ ρ.val ≠ ⊤ := by
    have h : AnalyticOnNhd ℂ riemannZeta₁ univ := fun s _ => hZ s
    exact h.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ (1:ℂ)) (mem_univ ρ.val)
      (by rw [analyticOrderAt_eq_zero.mpr (Or.inr (by simp : riemannZeta₁ 1 ≠ 0))]; simp)
  have ho := (hZ ρ.val).analyticOrderAt_deriv_add_one
  simp only [hzero,sub_zero] at ho
  rw [analyticOrderAt_congr hloc,analyticOrderAt_mul (hZ ρ.val) (hco _ hρ)] at ho
  have hle : analyticOrderAt riemannZeta₁ ρ.val + 1 ≤ analyticOrderAt riemannZeta₁ ρ.val := by
    calc _ ≤ (analyticOrderAt riemannZeta₁ ρ.val+analyticOrderAt odeCoeff ρ.val)+1 := by gcongr; exact le_self_add ..
         _ = _ := ho
  exact ((ENat.lt_add_one_iff hfin).mpr le_rfl).not_ge hle

private theorem usual_RH : RiemannHypothesis ↔ ∀ z : Z,z.val.re ≤ 1/2 := by
  rw [riemannHypothesis_iff_zeros_in_strip_on_line]
  constructor
  · exact fun h z => (h z.val z.prop.1 z.prop.2.1 z.prop.2.2.1).le
  · intro h s hzero h0 h1
    let z : Z := ⟨s,hzero,h0,h1,abs_lt.mpr ⟨by linarith,by linarith⟩⟩
    have hu : s.re ≤ 1/2 := h z
    have hnot (n : ℕ) : s ≠ -n := by
      intro he; have hr := congrArg Complex.re he; simp only [Complex.neg_re,Complex.natCast_re] at hr
      linarith [n.cast_nonneg (α:=ℝ)]
    have hne : s ≠ 1 := fun he => by simp [he] at h1
    have hz' : riemannZeta (1-s)=0 := by rw [riemannZeta_one_sub hnot hne,hzero,mul_zero]
    have h0' : 0 < (1-s).re := by simp; linarith
    have h1' : (1-s).re < 1 := by simp; linarith
    let z' : Z := ⟨1-s,hz',h0',h1',abs_lt.mpr ⟨by linarith,by linarith⟩⟩
    have hl : (1-s).re ≤ 1/2 := h z'
    rw [Complex.sub_re,Complex.one_re] at hl
    linarith

end RampEnergyProof
open RampEnergyProof

theorem solution :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let F (θ u : ℝ) := G (Real.exp u)*Real.exp (-(θ*u))/(1+u)
    (∀ θ : ℝ, 0 ≤ θ → θ < 1 →
        ((∀ z : ZetaZerosInTraceStrip (1/2), z.val.re ≤ θ) ↔
           IntegrableOn (fun u => (F θ u)^2) (Ioi (0:ℝ)))) ∧
    (RiemannHypothesis ↔ IntegrableOn (fun u => (F (1/2) u)^2) (Ioi (0:ℝ))) ∧
    (∀ θ : ℝ, 0 ≤ θ → (∀ z : ZetaZerosInTraceStrip (1/2), z.val.re ≤ θ) →
        (∫ u in Ioi (0:ℝ),(F θ u)^2) ≤ 81) := by
  have main (θ : ℝ) (hθ : 0 ≤ θ) (h1 : θ < 1) :
      (∀ z : Z,z.val.re ≤ θ) ↔ Integrable (fun u => (profile θ u)^2) μ := by
    rw [←memLp_two_iff_integrable_sq (measprofile θ).aestronglyMeasurable]
    exact ⟨fun hz => (energy_of_bound hθ hz).1,bound_of_energy h1⟩
  exact ⟨main,usual_RH.trans (main (1/2) (by norm_num) (by norm_num)),
    fun θ hθ hz => (energy_of_bound hθ hz).2⟩

end
