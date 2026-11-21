-- Prove2me | solution 1 for MasulloRH.prime_ramp_absolute_explicit_formula
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:06:24.83518+00:00
-- url     : https://prove2.me/submissions/1bbc001a-2276-4d51-8da5-b295b6b845e7

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_prime_ramp_integrated_explicit_formula
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Mathlib
open Filter Finset Set Topology MeasureTheory ArithmeticFunction
open scoped Interval
noncomputable section
open MasulloRH
namespace RampAbsoluteProof

private abbrev Z := ZetaZerosInTraceStrip (1/2)
private abbrev B : ℝ := 0.8749570698
private def G (x : ℝ) : ℝ := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
    x*(Real.log x-1-Real.eulerMascheroniConstant)
private def K (x : ℝ) (z : Z) : ℂ := (analyticOrderNatAt riemannZeta z.val : ℂ) * (x:ℂ)^(z.val-1)/(z.val*(z.val-1))
private def S (x : ℝ) : ℂ := ∑' z : Z,K x z
private def A (t : ℝ) : ℝ := (Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))/t^2
private def tail (x : ℝ) : ℝ := ∫ t in Ioi x,A t
private def C₀ : ℝ := |Real.log (2*Real.pi)|+|Real.log (1/2)|

private theorem zero_upper (z : Z) : z.val.re ≤ B := by
  by_contra! h
  have hne : z.val ≠ 1 := fun he => by have := z.prop.2.2.1; simpa [he] using this
  have hfree := TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound (1 : DirichletCharacter ℂ 1) h (fun he => hne he.2)
  simpa [z.prop.1] using hfree

private theorem Knorm_sum {x : ℝ} (hx : 1≤x) : Summable (fun z => ‖K x z‖) :=
  prime_ramp_integrated_explicit_formula.1 x hx

private theorem K_bound {x : ℝ} (hx : 1≤x) {θ : ℝ} (z : Z) (hz : z.val.re≤θ) :
    ‖K x z‖ ≤ x^(θ-1)*‖K 1 z‖ := by
  have hx0 : 0<x := by linarith
  unfold K
  simp only [Complex.ofReal_one,Complex.one_cpow,mul_one,norm_mul,norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have h : x^(z.val-1).re ≤ x^(θ-1) := Real.rpow_le_rpow_of_exponent_le hx (by simp; linarith [hz])
  calc _ ≤ (‖(analyticOrderNatAt riemannZeta z.val:ℂ)‖*x^(θ-1))/(‖z.val‖*‖z.val-1‖) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (norm_nonneg _)) (by positivity)
       _ = _ := by ring

private theorem S_bound_for {x θ : ℝ} (hx : 1≤x) (hz : ∀ z : Z, z.val.re≤θ) :
    ‖S x‖ ≤ x^(θ-1)*(∑' z : Z,‖K 1 z‖) := by
  calc ‖S x‖ ≤ ∑' z : Z,‖K x z‖ := norm_tsum_le_tsum_norm (Knorm_sum hx)
       _ ≤ ∑' z : Z,x^(θ-1)*‖K 1 z‖ := (Knorm_sum hx).tsum_le_tsum (fun z => K_bound hx z (hz z)) ((Knorm_sum (x:=1) le_rfl).mul_left _)
       _ = _ := tsum_mul_left

private theorem S_bound {x : ℝ} (hx : 1≤x) :
    ‖S x‖ ≤ x^(B-1)*(∑' z : Z,‖K 1 z‖) := S_bound_for hx zero_upper

private theorem S_limit : Tendsto S atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ((eventually_ge_atTop 1).mono fun _ hx => S_bound hx)
  have h := (tendsto_rpow_neg_atTop (by norm_num [B] : 0<1-B)).mul_const (∑' z : Z,‖K 1 z‖)
  simpa only [neg_sub,zero_mul] using h

private theorem A_bound {t : ℝ} (ht : 2≤t) : ‖A t‖ ≤ C₀*t^(-2:ℝ) := by
  have ht0 : 0<t := by linarith
  have hi : 0 < (t^2)⁻¹ := by positivity
  have hi' : (t^2)⁻¹ ≤ 1/2 := by
    rw [inv_eq_one_div]; apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hlow : Real.log (1/2) ≤ Real.log (1-(t^2)⁻¹) := Real.log_le_log (by norm_num) (by linarith)
  have hup : Real.log (1-(t^2)⁻¹) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hl : |Real.log (1-(t^2)⁻¹)| ≤ |Real.log (1/2)| := by rw [abs_of_nonpos hup,abs_of_nonpos (hlow.trans hup)]; linarith
  unfold A C₀
  rw [Real.rpow_neg ht0.le,Real.rpow_two,Real.norm_eq_abs,abs_div,abs_of_nonneg (sq_nonneg t),div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ hi.le
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  linarith [abs_nonneg (Real.log (1-(t^2)⁻¹))]

private theorem A_ible {x : ℝ} (hx : 2≤x) : IntegrableOn A (Ioi x) := by
  have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) (by linarith : 0<x)).const_mul C₀
  have hm : Measurable A := by unfold A; fun_prop
  apply h.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact A_bound (hx.trans (le_of_lt ht))

private theorem tail_bound {x : ℝ} (hx : 2≤x) : ‖tail x‖ ≤ C₀/x := by
  have hx0 : 0<x := by linarith
  unfold tail
  apply (norm_integral_le_integral_norm _).trans
  calc _ ≤ ∫ t in Ioi x,C₀*t^(-2:ℝ) := by
          apply integral_mono_ae (A_ible hx).norm ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hx0).const_mul C₀)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using A_bound (hx.trans (le_of_lt ht))
       _ = _ := by rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) hx0]; norm_num [div_eq_mul_inv,Real.rpow_neg_one]

private theorem tail_limit : Tendsto tail atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ((eventually_ge_atTop 2).mono fun _ hx => tail_bound hx) (tendsto_const_nhds.div_atTop tendsto_id)

private def d : ℂ := ((G 2/2:ℝ):ℂ)+S 2-(tail 2:ℂ)

private theorem compensated {x : ℝ} (hx : 2≤x) :
    ((G x/x:ℝ):ℂ) = d-S x+(tail x:ℂ) := by
  have h := prime_ramp_integrated_explicit_formula.2 2 x (by norm_num) hx
  change ((G x/x - G 2/2:ℝ):ℂ) + (∑' z : Z,(K x z-K 2 z)) + _ = 0 at h
  rw [Summable.tsum_sub ((Knorm_sum (by linarith : 1≤x)).of_norm)
    ((Knorm_sum (by norm_num : (1:ℝ)≤2)).of_norm)] at h
  have hi : (∫ t in (2:ℝ)..x, ((Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)):ℝ):ℂ)/(t:ℂ)^2) =
      (↑(∫ t in (2:ℝ)..x,A t):ℂ) := by
    rw [←intervalIntegral.integral_ofReal]; simp only [A,Complex.ofReal_div,Complex.ofReal_pow]
  rw [hi] at h
  have ht : (∫ t in (2:ℝ)..x,A t) + tail x = tail 2 := intervalIntegral.integral_interval_add_Ioi (A_ible (by norm_num)) (A_ible hx)
  have hc := congrArg Complex.ofReal ht
  simp only [Complex.ofReal_add] at hc
  change _ + (S x-S 2) + _ = 0 at h
  rw [Complex.ofReal_sub] at h
  unfold d
  linear_combination h - hc

private theorem ratio_limit : Tendsto (fun x : ℝ => G x / x) atTop (𝓝 d.re) := by
  have hl := ((tendsto_const_nhds (x:=d)).sub S_limit).add (Complex.continuous_ofReal.continuousAt.tendsto.comp tail_limit)
  have hc : Tendsto (fun x : ℝ => ((G x/x:ℝ):ℂ)) atTop (𝓝 d) := by
    simpa only [sub_zero,Complex.ofReal_zero,add_zero] using
      hl.congr' ((eventually_ge_atTop 2).mono fun x hx => (compensated hx).symm)
  exact Complex.continuous_re.continuousAt.tendsto.comp hc

private theorem ratio_bounded : ∃ M : ℝ, 0≤M ∧ ∀ x : ℝ, 1≤x → |G x/x|≤M := by
  let W := ∑' z : Z, ‖K 1 z‖
  have hW : 0≤W := tsum_nonneg (fun _ => norm_nonneg _)
  have hC : 0≤C₀ := add_nonneg (abs_nonneg _) (abs_nonneg _)
  let M := ‖d‖+W+C₀+Real.log 2+1+|Real.eulerMascheroniConstant|
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro x hx
  have hx0 : 0<x := by linarith
  by_cases h2 : 2≤x
  · have hs : ‖S x‖ ≤ W := (S_bound hx).trans (mul_le_of_le_one_left hW (Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num [B])))
    have ht : ‖tail x‖ ≤ C₀ := (tail_bound h2).trans (div_le_self hC hx)
    have he : |G x/x| = ‖d-S x+(tail x:ℂ)‖ := by rw [←compensated h2,Complex.norm_real,Real.norm_eq_abs]
    rw [he]
    have hsum := norm_add_le (d-S x) (tail x:ℂ)
    have hsub := norm_sub_le d (S x)
    rw [Complex.norm_real] at hsum
    dsimp [M]; linarith [abs_nonneg Real.eulerMascheroniConstant]
  · have hfl : ⌊x⌋₊=1 := Nat.floor_eq_iff (by linarith : 0≤x) |>.mpr ⟨by simpa,by norm_num; exact lt_of_not_ge h2⟩
    have he : G x/x = -(Real.log x-1-Real.eulerMascheroniConstant) := by
      simp [G,hfl,Finset.sum_range_succ]; field_simp; ring
    rw [he,abs_neg]
    have hlog := Real.log_nonneg hx
    have hlog2 := Real.log_le_log hx0 (le_of_lt (lt_of_not_ge h2))
    dsimp [M]; exact abs_le.mpr ⟨by linarith [norm_nonneg d,le_abs_self Real.eulerMascheroniConstant],
       by linarith [norm_nonneg d,neg_abs_le Real.eulerMascheroniConstant]⟩

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

private def Htest (h v : ℝ) : ℂ := ((G (Real.exp (h*v))/Real.exp (h*v):ℝ):ℂ)*(Real.exp (-v):ℂ)

private theorem average_limit :
    Tendsto (fun h : ℝ => ∫ v in Ioi (0:ℝ),Htest h v) atTop (𝓝 (d.re:ℂ)) := by
  obtain ⟨M,hM,hB⟩ := ratio_bounded
  have hG : Measurable G := zetaRampError_measurable
  have hm (h : ℝ) : Measurable (Htest h) := by unfold Htest; fun_prop
  have hmass : (∫ v in Ioi (0:ℝ),Real.exp (-v)) = 1 := by
    simpa using integral_exp_mul_Ioi (a:=(-1:ℝ)) (by norm_num) 0
  have hI : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (a:=(-1:ℝ)) (by norm_num) 0
  have hdct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ:=volume.restrict (Ioi (0:ℝ))) (l:=(atTop : Filter ℝ))
    (F:=Htest) (f:=fun v => (d.re:ℂ)*(Real.exp (-v):ℂ))
    (fun v => M*Real.exp (-v))
    (Eventually.of_forall fun h => (hm h).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with h hh
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      simp only [Htest,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos (-v))]
      exact mul_le_mul_of_nonneg_right (hB _ (Real.one_le_exp (mul_nonneg hh (le_of_lt hv)))) (Real.exp_nonneg _))
    (hI.const_mul M)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hlim := ratio_limit.comp (Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const (show 0<v from hv)))
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hlim).mul_const _)
  simpa only [integral_const_mul,integral_complex_ofReal,hmass,Complex.ofReal_one,mul_one] using hdct

private theorem average_eq {h : ℝ} (hh : 0<h) :
    (∫ v in Ioi (0:ℝ),Htest h v) = ((h:ℂ)⁻¹)*zetaWindowTransform (1+((h⁻¹:ℝ):ℂ)) := by
  let s : ℂ := 1+((h⁻¹:ℝ):ℂ)
  have hs : 1<s.re := by dsimp [s]; simp [Complex.add_re,hh]
  let f (u : ℝ) := (G (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))
  have hf : (∫ u in Ioi (0:ℝ),f u) = zetaWindowTransform s :=
    (zetaRampError_laplace hs).trans (zetaWindowTransform_eq_logDerivative hs).symm
  have he (v : ℝ) : Htest h v = f (h*v) := by
    have hexp : -s*((h*v:ℝ):ℂ) = -((h*v:ℝ):ℂ)+(-(v:ℂ)) := by
      dsimp [s]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hh.ne']
      <;> ring
    unfold Htest f
    rw [hexp,Complex.exp_add,Complex.exp_neg,← Complex.ofReal_exp]
    push_cast
    rw [Complex.exp_neg]
    ring
  simp only [he,integral_comp_mul_left_Ioi f (0:ℝ) hh,mul_zero,hf,Complex.real_smul]
  simp [s]

private theorem vanishing_constant : d=0 := by
  have hi : Tendsto (fun h : ℝ => h⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hc : Tendsto (fun h : ℝ => ((h⁻¹:ℝ):ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hi
  have hs : Tendsto (fun h : ℝ => 1+((h⁻¹:ℝ):ℂ)) atTop (𝓝 1) := by simpa using hc.const_add (1:ℂ)
  have hW := (zetaWindowTransform_differentiableAt (s:=1) (by norm_num) riemannZeta_one_ne_zero).continuousAt.tendsto.comp hs
  have hlim : Tendsto (fun h : ℝ => ∫ v in Ioi (0:ℝ),Htest h v) atTop (𝓝 0) := by
    have ht := hc.mul hW
    simp only [zero_mul] at ht
    exact ht.congr' ((eventually_gt_atTop (0:ℝ)).mono fun h hh => by simp only [Function.comp_apply]; simpa only [Complex.ofReal_inv] using (average_eq hh).symm)
  have hr : (d.re:ℂ)=0 := tendsto_nhds_unique average_limit hlim
  have hr' : d.re=0 := Complex.ofReal_eq_zero.mp hr
  have hL := Complex.continuous_ofReal.continuousAt.tendsto.comp ratio_limit
  have hc' : Tendsto (fun x : ℝ => ((G x/x:ℝ):ℂ)) atTop (𝓝 0) := by simpa only [hr',Function.comp_def,Complex.ofReal_zero] using hL
  have ht := ((tendsto_const_nhds (x:=d)).sub S_limit).add (Complex.continuous_ofReal.continuousAt.tendsto.comp tail_limit)
  have hd : Tendsto (fun x : ℝ => ((G x/x:ℝ):ℂ)) atTop (𝓝 d) := by
    simpa only [sub_zero,Complex.ofReal_zero,add_zero] using ht.congr' ((eventually_ge_atTop 2).mono fun x hx => (compensated hx).symm)
  exact tendsto_nhds_unique hd hc'

private theorem direct_bound {θ x : ℝ} (hθ : 0≤θ) (hz : ∀ z : Z,z.val.re≤θ) (hx : 2≤x) :
    |G x| ≤ ((∑' z : Z,‖K 1 z‖)+C₀)*x^θ := by
  let W := ∑' z : Z, ‖K 1 z‖
  have hx1 : 1≤x := by linarith
  have hx0 : 0<x := by linarith
  have hθx := Real.one_le_rpow hx1 hθ
  have hpos : 0≤C₀ := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hr : |G x/x| ≤ x^(θ-1)*W + C₀/x := by
    have he := compensated hx
    rw [vanishing_constant,zero_sub] at he
    have h := norm_add_le (-S x) (tail x:ℂ)
    rw [←he,Complex.norm_real,Real.norm_eq_abs,norm_neg,Complex.norm_real] at h
    exact h.trans (add_le_add (S_bound_for hx1 hz) (tail_bound hx))
  rw [abs_div,abs_of_pos hx0,div_le_iff₀ hx0] at hr
  have he : x^(θ-1)*x=x^θ := by
    conv_lhs => arg 2; rw [←Real.rpow_one x]
    rw [←Real.rpow_add hx0]; congr 1; ring
  calc |G x| ≤ _ := hr
       _ = W*x^θ+C₀ := by
         rw [add_mul,div_mul_cancel₀ _ hx0.ne',←he]; ring
       _ ≤ (W+C₀)*x^θ := by rw [add_mul]; linarith [mul_le_mul_of_nonneg_left hθx hpos]

end RampAbsoluteProof
open RampAbsoluteProof

theorem solution :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let K (x : ℝ) (ρ : ZetaZerosInTraceStrip (1/2)) :=
      (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (x:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1))
    let C : ℝ := (∑' ρ : ZetaZerosInTraceStrip (1/2),‖K 1 ρ‖) + (|Real.log (2*Real.pi)|+|Real.log (1/2)|)
    (∀ x : ℝ, 2≤x →
      ((G x/x:ℝ):ℂ) = -(∑' ρ : ZetaZerosInTraceStrip (1/2),K x ρ) +
        ((∫ t in Ioi x,(Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))/t^2 : ℝ):ℂ)) ∧
    (∀ θ : ℝ, 0≤θ → (∀ ρ : ZetaZerosInTraceStrip (1/2),ρ.val.re≤θ) →
      ∀ x : ℝ, 2≤x → |G x|≤C*x^θ) ∧
    (∀ x : ℝ, 2≤x → |G x|≤C*x^(0.8749570698:ℝ)) := by
  constructor
  · intro x hx
    change ((G x/x:ℝ):ℂ) = -S x+(tail x:ℂ)
    simpa only [vanishing_constant,zero_sub] using compensated hx
  · exact ⟨fun θ hθ hz x hx => direct_bound hθ hz hx,fun x hx => direct_bound (by norm_num [B] : 0≤B) zero_upper hx⟩

end
