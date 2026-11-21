-- Prove2me | solution 1 for MasulloRH.rational_theta_test_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:13:19.185758+00:00
-- url     : https://prove2.me/submissions/3e51f3c5-7d5a-45e2-bd55-d68cac7f110e

import Mathlib

open Set Filter MeasureTheory Asymptotics
open scoped Topology SchwartzMap FourierTransform
namespace MasulloRH
noncomputable section

private lemma absInt_scale (f : ℝ → ℂ) (s : ℂ) (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1) • f (a*x)‖ =
      a^(-s.re) * ∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1) • f x‖ := by
  let F (u : ℝ) := ‖(u:ℂ)^(s-1) • f u‖
  have hpow : (a^(s.re-1))⁻¹ * a⁻¹ = a^(-s.re) := by
    rw [← Real.rpow_neg ha.le, ← Real.rpow_neg_one, ← Real.rpow_add ha]
    congr 1; ring
  calc
    _ = ∫ x : ℝ in Ioi 0, (a^(s.re-1))⁻¹ * F (a*x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 0 < x at hx
      simp only [F, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
        Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos ha hx), Complex.sub_re, Complex.one_re, Real.mul_rpow ha.le hx.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos ha (s.re-1))]
    _ = _ := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi F 0 ha, mul_zero, smul_eq_mul, ← mul_assoc, hpow]

/-- The Mellin transform of the positive integral dilates of an arbitrary test function,
in the half-plane of absolute Dirichlet convergence. -/
lemma mellin_pos_dilates (f : ℝ → ℂ) (s : ℂ) (hs : 1 < s.re) (hf : MellinConvergent f s) :
    mellin (fun x : ℝ => ∑' n : ℕ, f (((n:ℝ)+1)*x)) s = riemannZeta s * mellin f s := by
  let F (n : ℕ) (x : ℝ) : ℂ := (x:ℂ)^(s-1) • f (((n:ℝ)+1)*x)
  have hInt (n : ℕ) : Integrable (F n) (volume.restrict (Ioi 0)) :=
    (MellinConvergent.comp_mul_left (f:=f) (s:=s) (a:=(n:ℝ)+1) (by positivity)).mpr hf
  have hSum : Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0, ‖F n x‖) := by
    have h₀ : Summable (fun n : ℕ => ((n:ℝ)+1)^(-s.re)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    apply (h₀.mul_right (∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1) • f x‖)).congr
    intro n
    exact (absInt_scale f s ((n:ℝ)+1) (by positivity)).symm
  have he := hasSum_integral_of_summable_integral_norm hInt hSum
  calc
    _ = ∫ x : ℝ in Ioi 0, ∑' n, F n x := by simp [mellin,F,tsum_mul_left,smul_eq_mul]
    _ = ∑' n, ∫ x : ℝ in Ioi 0, F n x := he.tsum_eq.symm
    _ = ∑' n : ℕ, (1/((n:ℂ)+1)^s)*mellin f s := by
      apply tsum_congr
      intro n
      change mellin (fun x => f (((n:ℝ)+1)*x)) s = _
      rw [mellin_comp_mul_left f s (by positivity : (0:ℝ)<n+1)]
      simp [Complex.cpow_neg,smul_eq_mul]
    _ = _ := by rw [tsum_mul_right, zeta_eq_tsum_one_div_nat_add_one_cpow hs]

private def latticeWeight (k : ℕ) (n : ℕ) : ℝ := (((n:ℝ)+1)^k)⁻¹

private lemma summable_latticeWeight (k : ℕ) (hk : 1 < k) : Summable (latticeWeight k) := by
  have h : -((k:ℕ):ℝ) < -1 := by exact_mod_cast (show -((k:ℕ):ℤ) < -1 by omega)
  have hz := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr h)
  apply hz.congr
  intro n
  dsimp [latticeWeight]
  rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg (by positivity), Real.rpow_natCast]

def thetaNat (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℕ, f (((n:ℝ)+1)*x)

private lemma thetaTerm_bound (f : 𝓢(ℝ,ℂ)) (k n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖f (((n:ℝ)+1)*x)‖ ≤ ((SchwartzMap.seminorm ℝ k 0) f) * (x^k)⁻¹ * latticeWeight k n := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ f k (((n:ℝ)+1)*x)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hn hx), mul_pow] at h
  rw [latticeWeight, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hn _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos hx _)]
  nlinarith only [h]

private lemma thetaNat_summable (f : 𝓢(ℝ,ℂ)) (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => f (((n:ℝ)+1)*x)) :=
  ((summable_latticeWeight 2 (by norm_num)).mul_left _).of_norm_bounded (fun n => thetaTerm_bound f 2 n hx)

private lemma thetaNat_bound (f : 𝓢(ℝ,ℂ)) (k : ℕ) (hk : 1 < k) {x : ℝ} (hx : 0 < x) :
    ‖thetaNat f x‖ ≤ (((SchwartzMap.seminorm ℝ k 0) f) * ∑' n, latticeWeight k n) * (x^k)⁻¹ := by
  apply (norm_tsum_le_tsum_norm ((thetaNat_summable f x hx).norm)).trans
  apply (Summable.tsum_le_tsum (fun n => thetaTerm_bound f k n hx) (thetaNat_summable f x hx).norm
    ((summable_latticeWeight k hk).mul_left _)).trans_eq
  rw [tsum_mul_left]; ring

lemma thetaNat_continuousOn (f : 𝓢(ℝ,ℂ)) : ContinuousOn (thetaNat f) (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  have hu : Summable (fun n : ℕ => (SchwartzMap.seminorm ℝ 2 0 f) * ((x/2)^2)⁻¹ * latticeWeight 2 n) :=
    (summable_latticeWeight 2 (by norm_num)).mul_left _
  have hc : ContinuousOn (thetaNat f) (Ioi (x/2)) := by
    apply continuousOn_tsum (fun n => (f.continuous.comp (continuous_const.mul continuous_id)).continuousOn) hu
    intro n y hy
    have hx' : 0 < x/2 := by positivity
    have hy' : x/2 < y := hy
    apply (thetaTerm_bound f 2 n (lt_trans hx' hy')).trans
    gcongr
    dsimp [latticeWeight]; positivity
  exact ((hc.continuousAt (isOpen_Ioi.mem_nhds (show x/2 < x by linarith)))).continuousWithinAt

def reflectS (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f

def theta (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℤ, f ((n:ℝ)*x)

lemma theta_split (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) {x : ℝ} (hx : 0 < x) :
    theta f x = thetaNat (f + reflectS f) x := by
  have h₁ := thetaNat_summable f x hx
  have h₂ := thetaNat_summable (reflectS f) x hx
  have hpos : Summable (fun n : ℕ => f ((((n:ℤ)+1 : ℤ) : ℝ)*x)) := by simpa using h₁
  have hneg : Summable (fun n : ℕ => f (((-((n:ℤ)+1) : ℤ) : ℝ)*x)) := by
    apply h₂.congr
    intro n
    change f (-(((n:ℝ)+1)*x)) = _
    push_cast; congr 1; ring
  have hsum := tsum_of_add_one_of_neg_add_one (f:=fun n : ℤ => f ((n:ℝ)*x)) hpos hneg
  change (∑' n : ℤ, f ((n:ℝ)*x)) = _
  rw [hsum]
  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast, Int.cast_neg, Int.cast_zero, zero_mul, hf, add_zero]
  change _ = ∑' n : ℕ, (f (((n:ℝ)+1)*x) + f (-(((n:ℝ)+1)*x)))
  rw [h₁.tsum_add (g:=fun n : ℕ => f (-(((n:ℝ)+1)*x))) h₂]
  simp only [neg_mul]

/-- Uniform positive-scale decay of the Schwartz lattice sum in every integral order above one. -/
theorem thetaSchwartz_bound (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖∑' n : ℤ, f ((n:ℝ)*x)‖ ≤ C * (x^k)⁻¹ := by
  refine ⟨(SchwartzMap.seminorm ℝ k 0) (f+reflectS f) * ∑' n, latticeWeight k n, ?_, ?_⟩
  · apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro n; dsimp [latticeWeight]; positivity
  · intro x hx
    change ‖theta f x‖ ≤ _
    rw [theta_split f hf hx]
    exact thetaNat_bound _ k hk hx

end
end MasulloRH

open MeasureTheory Filter Set FourierTransform
open scoped SchwartzMap FourierTransform Topology
set_option autoImplicit false
namespace MasulloSynthesis
noncomputable section

theorem theta_poisson_scaled (f : 𝓢(ℝ,ℂ)) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, f ((n:ℝ)*a)) =
    (a⁻¹:ℝ) • ∑' n : ℤ, (𝓕 f) ((n:ℝ)*a⁻¹) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha.ne')
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hg (x : ℝ) : g x = f (a*x) := rfl
  have hscale (ξ : ℝ) : (𝓕 g) ξ = (a⁻¹:ℝ) • (𝓕 f) (ξ*a⁻¹) := by
    change 𝓕 (⇑g) ξ = (a⁻¹:ℝ) • 𝓕 (⇑f) (ξ*a⁻¹)
    rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
    let F (x : ℝ) := Complex.exp (↑(-2*Real.pi*x*(ξ*a⁻¹)) * Complex.I) • f x
    calc
      _ = ∫ x : ℝ, F (a*x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [F]
          rw [hg]
          congr 3
          field_simp
      _ = _ := by
        have h := Measure.integral_comp_mul_left F a
        simpa only [abs_of_pos (inv_pos.mpr ha)] using h
  have h := g.tsum_eq_tsum_fourier 0
  simp only [zero_add, hg, hscale, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at h
  rw [← tsum_const_smul'']
  simpa [mul_comm a] using h
theorem theta_poisson_near_zero (f : 𝓢(ℝ,ℂ)) (hI : (∫ x : ℝ, f x) = 0) :
    (fun x : ℝ => ∑' n : ℤ, f ((n:ℝ)*x)) =O[𝓝[>] (0:ℝ)] (fun _ : ℝ => (1:ℝ)) := by
  have hF0 : (𝓕 f : 𝓢(ℝ,ℂ)) 0 = 0 := by
    change 𝓕 (⇑f) 0 = 0
    simpa [Real.fourier_real_eq_integral_exp_smul] using hI
  obtain ⟨C,hC,hbound⟩ := MasulloRH.thetaSchwartz_bound (𝓕 f) hF0 2 (by decide)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))] with x hx hx1
  have hpos : 0 < x := hx
  have hxle : x ≤ 1 := le_of_lt hx1
  change ‖∑' n : ℤ, f ((n:ℝ)*x)‖ ≤ C * ‖(1:ℝ)‖
  rw [theta_poisson_scaled f hpos, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hpos).le]
  simp only [norm_one, mul_one]
  calc
    _ ≤ x⁻¹ * (C * ((x⁻¹)^2)⁻¹) := mul_le_mul_of_nonneg_left (hbound _ (inv_pos.mpr hpos)) (inv_pos.mpr hpos).le
    _ = C * x := by field_simp
    _ ≤ C := mul_le_of_le_one_right hC hxle
end
end MasulloSynthesis

open Set Filter MeasureTheory Asymptotics
open scoped Topology SchwartzMap
namespace MasulloRH
noncomputable section

private lemma halfspace_mellin (f : ℝ → ℂ) (hl : LocallyIntegrableOn f (Ioi 0))
    (hb : f =O[𝓝[>] (0:ℝ)] (fun _ : ℝ => (1:ℝ)))
    (ht : ∀ u : ℝ, ∃ a : ℝ, u < a ∧ f =O[atTop] (fun x : ℝ => x^(-a))) :
    (∀ s : ℂ, 0 < s.re → MellinConvergent f s) ∧ AnalyticOnNhd ℂ (mellin f) {s : ℂ | 0 < s.re} := by
  have hb' : f =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-(0:ℝ))) := by simpa using hb
  constructor
  · intro s hs
    obtain ⟨a,ha,ht⟩ := ht s.re
    exact mellinConvergent_of_isBigO_rpow hl ht ha hb' hs
  · apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    obtain ⟨a,ha,ht⟩ := ht s.re
    exact (mellin_differentiableAt_of_isBigO_rpow hl ht ha hb' hs).differentiableWithinAt

private lemma schwartz_halfspace_mellin (f : 𝓢(ℝ,ℂ)) :
    (∀ s : ℂ, 0 < s.re → MellinConvergent f s) ∧ AnalyticOnNhd ℂ (mellin f) {s : ℂ | 0 < s.re} := by
  apply halfspace_mellin _ (f.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    ((f.continuous.tendsto 0).mono_left nhdsWithin_le_nhds |>.isBigO_one ℝ)
  intro u
  refine ⟨u+1, by linarith, ?_⟩
  apply ((f.isBigO_cocompact_rpow (-(u+1))).mono atTop_le_cocompact).congr' .rfl
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  rw [Real.norm_of_nonneg hx]

private lemma theta_halfspace_mellin (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0)
    (hb : theta f =O[𝓝[>] (0:ℝ)] (fun _ : ℝ => (1:ℝ))) :
    (∀ s : ℂ, 0 < s.re → MellinConvergent (theta f) s) ∧ AnalyticOnNhd ℂ (mellin (theta f)) {s : ℂ | 0 < s.re} := by
  refine halfspace_mellin _ ?_ hb ?_
  · have he : Set.EqOn (theta f) (thetaNat (f+reflectS f)) (Ioi 0) := fun _ hx => theta_split f hf hx
    exact ((thetaNat_continuousOn _).congr he).locallyIntegrableOn measurableSet_Ioi
  · intro u
    let k := ⌈u⌉₊+2
    have hk : 1 < k := by dsimp [k]; omega
    obtain ⟨C,_,hC⟩ := thetaSchwartz_bound f hf k hk
    refine ⟨k, ?_, isBigO_iff.mpr ⟨C, ?_⟩⟩
    · dsimp [k]; push_cast; linarith [Nat.le_ceil u]
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      simpa [theta, Real.rpow_neg hx.le, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hx.le k))] using hC x hx

private def zetaPolynomial (s : ℂ) : ℂ := s*(s-1)
private def entireZeta (s : ℂ) : ℂ := (zetaPolynomial s * completedRiemannZeta₀ s + 1) * (Complex.Gammaℝ s)⁻¹

private lemma entireZeta_apply (s : ℂ) (hs : s ≠ 0) (hs' : s ≠ 1) :
    entireZeta s = zetaPolynomial s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs, completedRiemannZeta_eq]
  unfold entireZeta zetaPolynomial
  rw [div_eq_mul_inv, ← mul_assoc]
  congr 1
  field_simp [hs, sub_ne_zero.mpr (Ne.symm hs')]
  ring

/-- Analytic continuation of the theta unfolding to the whole right half-plane punctured
at one, assuming only a bounded theta sum at the origin. -/
theorem theta_Mellin_of_bounded_at_zero (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0)
    (hb : (fun x : ℝ => ∑' n : ℤ, f ((n:ℝ)*x)) =O[𝓝[>] (0:ℝ)] (fun _ : ℝ => (1:ℝ)))
    (s : ℂ) (hs : 0 < s.re) (hs' : s ≠ 1) :
    HasMellin (fun x : ℝ => ∑' n : ℤ, f ((n:ℝ)*x)) s
      (riemannZeta s * mellin (fun x : ℝ => f x + f (-x)) s) := by
  let g := f+reflectS f
  let U := {z : ℂ | 0 < z.re}
  have hT := theta_halfspace_mellin f hf hb
  have hG := schwartz_halfspace_mellin g
  refine ⟨hT.1 s hs, ?_⟩
  have hleft : AnalyticOnNhd ℂ (fun z => zetaPolynomial z * mellin (theta f) z) U :=
    (show AnalyticOnNhd ℂ zetaPolynomial U by intro z hz; unfold zetaPolynomial; fun_prop).mul hT.2
  have hE : AnalyticOnNhd ℂ entireZeta U := by
    unfold entireZeta zetaPolynomial
    intro z hz
    apply AnalyticAt.mul _ (Complex.differentiable_Gammaℝ_inv.analyticAt z)
    exact (((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul (differentiable_completedZeta₀.analyticAt z)).add analyticAt_const)
  have he := hleft.eqOn_of_preconnected_of_eventuallyEq (hE.mul hG.2)
    (convex_halfSpace_re_gt 0).isPreconnected (z₀:=2) (by change 0 < (2:ℂ).re; norm_num) (by
      have hu : ∀ᶠ z : ℂ in 𝓝 2, 1 < z.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
      filter_upwards [hu] with z hz
      have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
      have hz1 : z ≠ 1 := by rintro rfl; norm_num at hz
      rw [entireZeta_apply z hz0 hz1, mul_assoc]
      apply congrArg (zetaPolynomial z * ·)
      calc
        mellin (theta f) z = mellin (thetaNat g) z := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact congrArg ((x:ℂ)^(z-1) • ·) (theta_split f hf hx)
        _ = _ := mellin_pos_dilates g z hz (hG.1 z (lt_trans zero_lt_one hz)))
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have h := he (show s ∈ U from hs)
  dsimp only at h
  rw [entireZeta_apply s hs0 hs', mul_assoc] at h
  exact mul_left_cancel₀ (mul_ne_zero hs0 (sub_ne_zero.mpr hs') : zetaPolynomial s ≠ 0) h

end
end MasulloRH

open Set Filter MeasureTheory Asymptotics
open scoped Topology SchwartzMap
namespace MasulloRH
noncomputable section

private lemma real_affine_order (f : ℂ → ℂ) (a b : ℂ) (hb : b ≠ 0) (t : ℝ)
    (hf : AnalyticAt ℂ f (a+b*(t:ℂ))) :
    analyticOrderAt (fun x : ℝ => f (a+b*(x:ℂ))) t = analyticOrderAt f (a+b*(t:ℂ)) := by
  let σ (x : ℝ) : ℂ := a+b*(x:ℂ)
  have ha : AnalyticAt ℝ σ t := analyticAt_const.add (analyticAt_const.mul (Complex.ofRealCLM.analyticAt t))
  change AnalyticAt ℂ f (σ t) at hf
  have hfR : AnalyticAt ℝ f (σ t) := hf.restrictScalars
  have hcomp : AnalyticAt ℝ (fun x : ℝ => f (σ x)) t := hfR.comp ha
  by_cases htop : analyticOrderAt f (σ t) = ⊤
  · rw [show a+b*(t:ℂ) = σ t by rfl, htop]
    exact analyticOrderAt_eq_top.mpr (ha.continuousAt.tendsto.eventually (analyticOrderAt_eq_top.mp htop))
  · let n := analyticOrderNatAt f (σ t)
    have hn : (n : ℕ∞) = analyticOrderAt f (σ t) := Nat.cast_analyticOrderNatAt htop
    rw [show a+b*(t:ℂ) = σ t by rfl, ← hn]
    apply hcomp.analyticOrderAt_eq_natCast.mpr
    obtain ⟨g,hg,hg0,he⟩ := hf.analyticOrderAt_eq_natCast.mp hn.symm
    refine ⟨fun x : ℝ => b^n*g (σ x), analyticAt_const.mul (hg.restrictScalars.comp ha),
      mul_ne_zero (pow_ne_zero _ hb) hg0, ?_⟩
    filter_upwards [ha.continuousAt.tendsto.eventually he] with x hx
    change f (σ x) = (σ x - σ t)^n • g (σ x) at hx
    rw [hx, smul_eq_mul, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_sub]
    dsimp [σ]
    rw [show a+b*(x:ℂ)-(a+b*(t:ℂ))=b*((x:ℂ)-(t:ℂ)) by ring, mul_pow]
    ring

private lemma theta_complexOrder (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) (hI : (∫ x : ℝ, f x) = 0)
    {s : ℂ} (hs : 0 < s.re) (hs' : s ≠ 1) :
    AnalyticAt ℂ (mellin (theta f)) s ∧
      analyticOrderAt riemannZeta s ≤ analyticOrderAt (mellin (theta f)) s := by
  have hb := MasulloSynthesis.theta_poisson_near_zero f hI
  have hA := (theta_halfspace_mellin f hf hb).2 s hs
  have hG := (schwartz_halfspace_mellin (f+reflectS f)).2 s hs
  have hζ := analyticOn_riemannZeta s (show s ∈ ({1}:Set ℂ)ᶜ from hs')
  have he : mellin (theta f) =ᶠ[𝓝 s] riemannZeta * mellin (⇑(f+reflectS f)) := by
    have hpos : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hpos, isOpen_ne.mem_nhds hs'] with z hz hz'
    exact (theta_Mellin_of_bounded_at_zero f hf hb z hz hz').2
  refine ⟨hA, ?_⟩
  rw [analyticOrderAt_congr he, analyticOrderAt_mul hζ hG]
  exact le_self_add

end
end MasulloRH

open MasulloRH

/-- Rational Tate factorization and annihilation of all admissible theta images
by the normalized critical-line jets below the order of a zeta zero. -/
private theorem rationalThetaTateHelper (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) (hI : (∫ x : ℝ, f x) = 0) :
    let Θ := fun x : ℝ => ∑' n : ℤ, f ((n:ℝ)*x)
    (∀ s : ℂ, 0 < s.re → s ≠ 1 →
      HasMellin Θ s (riemannZeta s * mellin (fun x : ℝ => f x + f (-x)) s) ∧
      analyticOrderAt riemannZeta s ≤ analyticOrderAt (mellin Θ) s) ∧
    ∀ ν : ℝ, let σ (x : ℝ) : ℂ := 1/2+((-2*Real.pi : ℝ):ℂ)*Complex.I*(x:ℂ)
      let M := fun x : ℝ => mellin Θ (σ x)
      AnalyticAt ℝ M ν ∧ analyticOrderAt riemannZeta (σ ν) ≤ analyticOrderAt M ν ∧
        ∀ j < analyticOrderNatAt riemannZeta (σ ν), iteratedDeriv j M ν = 0 := by
  dsimp only
  have hB := MasulloSynthesis.theta_poisson_near_zero f hI
  refine ⟨fun s hs hs' => ⟨theta_Mellin_of_bounded_at_zero f hf hB s hs hs',
    (theta_complexOrder f hf hI hs hs').2⟩, ?_⟩
  intro ν
  let a : ℂ := 1/2
  let b : ℂ := ((-2*Real.pi : ℝ):ℂ)*Complex.I
  let σ (x : ℝ) : ℂ := a+b*(x:ℂ)
  have hσ : (σ ν).re = 1/2 := by simp [σ,a,b,Complex.mul_re,Complex.mul_im]
  have hpos : 0 < (σ ν).re := by rw [hσ]; norm_num
  have hne : σ ν ≠ 1 := by intro h; rw [h] at hσ; norm_num at hσ
  have ⟨hA,hord⟩ := theta_complexOrder f hf hI hpos hne
  have ha : AnalyticAt ℝ σ ν := analyticAt_const.add (analyticAt_const.mul (Complex.ofRealCLM.analyticAt ν))
  have hAR : AnalyticAt ℝ (mellin (theta f)) (σ ν) := hA.restrictScalars
  have hM : AnalyticAt ℝ (fun z : ℝ => mellin (theta f) (σ z)) ν := hAR.comp ha
  have hb : b ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero
  have ho := hord.trans_eq (real_affine_order (mellin (theta f)) a b hb ν hA).symm
  refine ⟨hM, ho, ?_⟩
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hM).mp
    ((ENat.natCast_toNat_le_self (analyticOrderAt riemannZeta (σ ν))).trans ho)

open Set Filter MeasureTheory
open scoped Topology SchwartzMap FourierTransform ContDiff
namespace MasulloRH
noncomputable section

private def logEuler (g : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  (1 / 2 : ℂ) • g + SchwartzMap.smulLeftCLM ℂ Complex.ofReal (SchwartzMap.derivCLM ℂ ℂ g)

private lemma logEuler_apply (g : 𝓢(ℝ,ℂ)) (t : ℝ) :
    logEuler g t = (1/2:ℂ) * g t + (t:ℂ) * deriv g t := by
  simp [logEuler, SchwartzMap.smulLeftCLM_apply_apply (show Function.HasTemperateGrowth Complex.ofReal from Complex.ofRealCLM.hasTemperateGrowth), smul_eq_mul]

private def logTerm (g : 𝓢(ℝ,ℂ)) (n : ℕ) (x : ℝ) : ℂ :=
  (Real.exp (x/2) : ℂ) * g (((n:ℝ)+1)*Real.exp x)

private def logNat (g : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ := ∑' n : ℕ, logTerm g n x

private lemma logTerm_deriv (g : 𝓢(ℝ,ℂ)) (n : ℕ) (x : ℝ) :
    HasDerivAt (logTerm g n) (logTerm (logEuler g) n x) x := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (u/2)) (Real.exp (x/2)/2) x := by
    convert (Real.hasDerivAt_exp (x/2)).comp x ((hasDerivAt_id x).div_const 2) using 1 <;> try rfl
    all_goals ring
  have hc : HasDerivAt (fun u : ℝ => ((n:ℝ)+1)*Real.exp u) (((n:ℝ)+1)*Real.exp x) x :=
    (Real.hasDerivAt_exp x).const_mul _
  have h := he.ofReal_comp.mul ((g.hasDerivAt _).scomp x hc)
  convert h using 1 <;> try rfl
  all_goals try simp [logTerm, logEuler_apply, Complex.real_smul]
  all_goals ring

private lemma logTerm_summable (g : 𝓢(ℝ,ℂ)) (x : ℝ) : Summable (fun n => logTerm g n x) :=
  (thetaNat_summable g _ (Real.exp_pos x)).mul_left _

private lemma logTerm_bound (g : 𝓢(ℝ,ℂ)) (n : ℕ) (x : ℝ) :
    ‖logTerm g n x‖ ≤ (SchwartzMap.seminorm ℝ 2 0 g) * Real.exp (-3*x/2) * latticeWeight 2 n := by
  have h := thetaTerm_bound g 2 n (Real.exp_pos x)
  rw [logTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_nat_mul, ← Real.exp_neg]
  calc
    _ = (SchwartzMap.seminorm ℝ 2 0 g) * (Real.exp (x/2) * Real.exp (-(2*x))) * latticeWeight 2 n := by norm_num; ring
    _ = _ := by rw [← Real.exp_add]; congr 3; ring

private lemma logNat_deriv (g : 𝓢(ℝ,ℂ)) (x : ℝ) :
    HasDerivAt (logNat g) (logNat (logEuler g) x) x := by
  let C := (SchwartzMap.seminorm ℝ 2 0 (logEuler g)) * Real.exp (-3*(x-1)/2)
  have hsum : Summable (fun n => C * latticeWeight 2 n) :=
    (summable_latticeWeight 2 (by decide)).mul_left _
  apply hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioi (isPreconnected_Ioi (a:=x-1))
    (fun n y _ => logTerm_deriv g n y) ?_ (y₀:=x) (show x ∈ Ioi (x-1) by simp) (logTerm_summable g x)
    (show x ∈ Ioi (x-1) by simp)
  intro n y hy
  have hxy : x-1 < y := hy
  apply (logTerm_bound _ n y).trans
  dsimp only [C]
  have hE : Real.exp (-3*y/2) ≤ Real.exp (-3*(x-1)/2) := Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity)) (by dsimp [latticeWeight]; positivity)

private def logEulerIter : ℕ → 𝓢(ℝ,ℂ) → 𝓢(ℝ,ℂ)
  | 0, g => g
  | n+1, g => logEuler (logEulerIter n g)

private lemma logNat_iterated (g : 𝓢(ℝ,ℂ)) (n : ℕ) :
    iteratedDeriv n (logNat g) = logNat (logEulerIter n g) := by
  induction n with
  | zero => simp [logEulerIter]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun x => (logNat_deriv _ x).deriv

private lemma logNat_smooth (g : 𝓢(ℝ,ℂ)) : ContDiff ℝ ∞ (logNat g) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [logNat_iterated]
  exact fun x => (logNat_deriv _ x).differentiableAt

private lemma logNat_bound (g : 𝓢(ℝ,ℂ)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
    ‖logNat g x‖ ≤ C * Real.exp (-3*x/2) := by
  let C := SchwartzMap.seminorm ℝ 2 0 g * ∑' n, latticeWeight 2 n
  have h : 0 ≤ ∑' n, latticeWeight 2 n := tsum_nonneg (fun n => by dsimp [latticeWeight]; positivity)
  refine ⟨C, mul_nonneg (by positivity) h, fun x => ?_⟩
  apply (norm_tsum_le_tsum_norm (logTerm_summable g x).norm).trans
  apply (Summable.tsum_le_tsum (fun n => logTerm_bound g n x) (logTerm_summable g x).norm
    ((summable_latticeWeight 2 (by decide)).mul_left _)).trans_eq
  rw [tsum_mul_left]
  dsimp only [C]
  ring

private def thetaLogFun (g : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ := (Real.exp (x/2):ℂ) * theta g (Real.exp x)

private lemma thetaLog_split (g : 𝓢(ℝ,ℂ)) (hg : g 0=0) :
    thetaLogFun g = logNat (g + reflectS g) := by
  funext x
  rw [thetaLogFun, theta_split g hg (Real.exp_pos x), logNat]
  simp [logTerm,thetaNat,tsum_mul_left]

private lemma thetaLog_recip (g : 𝓢(ℝ,ℂ)) :
    thetaLogFun g = fun x => thetaLogFun (𝓕 g) (-x) := by
  funext x
  simp only [thetaLogFun, theta, MasulloSynthesis.theta_poisson_scaled g (Real.exp_pos x), Real.exp_neg,
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

private lemma logNat_halfline (g : 𝓢(ℝ,ℂ)) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖x‖^k * ‖iteratedDeriv n (logNat g) x‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := logNat_bound (logEulerIter n g)
  refine ⟨(k.factorial:ℝ)*C, ?_⟩
  intro x hx
  rw [logNat_iterated, Real.norm_of_nonneg hx]
  have hpow := (div_le_iff₀ (show 0 < (k.factorial:ℝ) by positivity)).mp (Real.pow_div_factorial_le_exp x hx k)
  apply (mul_le_mul hpow (h x) (norm_nonneg _) (by positivity)).trans
  calc
    _ = ((k.factorial:ℝ)*C) * Real.exp (x+(-3*x/2)) := by rw [Real.exp_add]; ring
    _ ≤ ((k.factorial:ℝ)*C) * 1 := by gcongr; exact Real.exp_le_one_iff.mpr (by linarith)
    _ = _ := mul_one _

private lemma thetaLog_schwartz (g : 𝓢(ℝ,ℂ)) (hg : g 0=0) (hI : (∫ t : ℝ, g t) = 0) :
    ∃ Θ : 𝓢(ℝ,ℂ), ∀ x : ℝ, Θ x = thetaLogFun g x := by
  have hF : (𝓕 g : 𝓢(ℝ,ℂ)) 0 = 0 := by
    change 𝓕 (⇑g) 0 = 0
    simpa [Real.fourier_real_eq_integral_exp_smul] using hI
  refine ⟨{toFun := thetaLogFun g, smooth' := by rw [thetaLog_split g hg]; exact logNat_smooth _, decay' := ?_}, fun _ => rfl⟩
  intro k n
  obtain ⟨C,hC⟩ := logNat_halfline (g+reflectS g) k n
  obtain ⟨D,hD⟩ := logNat_halfline (𝓕 g+reflectS (𝓕 g)) k n
  refine ⟨max C D, fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hx : 0 ≤ x
  · rw [thetaLog_split g hg]
    exact (hC x hx).trans (le_max_left _ _)
  · rw [thetaLog_recip g, thetaLog_split (𝓕 g) hF, iteratedDeriv_comp_neg]
    simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    simpa using (hD (-x) (by linarith)).trans (le_max_right C D)

private lemma thetaLog_fourier (g : 𝓢(ℝ,ℂ)) (ν : ℝ) :
    𝓕 (thetaLogFun g) ν = mellin (theta g) (1/2 + ((-2*Real.pi:ℝ):ℂ)*Complex.I*(ν:ℂ)) := by
  let s : ℂ := 1/2 + ((-2*Real.pi:ℝ):ℂ)*Complex.I*(ν:ℂ)
  have hs : s.re = 1/2 := by simp [s, Complex.mul_re, Complex.mul_im]
  have hi : s.im = -2*Real.pi*ν := by simp [s, Complex.mul_re, Complex.mul_im]
  change _ = mellin _ s
  rw [mellin_eq_fourier, hs, hi]
  have hfun : (fun u : ℝ => Real.exp (-(1/2)*u) • theta g (Real.exp (-u))) =
      fun u => thetaLogFun g (-u) := by
    funext u
    rw [thetaLogFun, Complex.real_smul]
    rw [show -(1 / 2 : ℝ) * u = -u / 2 by ring]
  rw [hfun, ← Real.fourierInv_eq_fourier_comp_neg (thetaLogFun g), Real.fourierInv_eq_fourier_neg]
  have heq : -(-2*Real.pi*ν/(2*Real.pi)) = ν := by field_simp [Real.pi_ne_zero]
  rw [heq]

/-- The normalized theta series of an admissible rational archimedean test, on the logarithmic
scale, is a Schwartz function whose Fourier transform is its critical-line Mellin transform. -/
theorem thetaLogSchwartz_exists (g : 𝓢(ℝ,ℂ)) (hg : g 0=0) (hI : (∫ t : ℝ, g t)=0) :
    ∃ Θ : 𝓢(ℝ,ℂ), (∀ x : ℝ, Θ x = (Real.exp (x/2):ℂ) * ∑' n : ℤ, g ((n:ℝ)*Real.exp x)) ∧
      ∀ ν : ℝ, (𝓕 Θ) ν = mellin (fun a : ℝ => ∑' n : ℤ, g ((n:ℝ)*a))
        (1/2+((-2*Real.pi:ℝ):ℂ)*Complex.I*(ν:ℂ)) := by
  obtain ⟨Θ,hΘ⟩ := thetaLog_schwartz g hg hI
  refine ⟨Θ,hΘ,fun ν => ?_⟩
  change 𝓕 (⇑Θ) ν = _
  rw [show (⇑Θ : ℝ → ℂ) = thetaLogFun g from funext hΘ]
  exact thetaLog_fourier g ν

end
end MasulloRH

/-- Tate factorization of the rational theta image, its genuine Schwartz logarithmic profile,
and full-order Fourier jet annihilation on the critical line. -/
theorem solution (g : 𝓢(ℝ,ℂ)) (hg : g 0 = 0) (hI : (∫ t : ℝ, g t) = 0) :
    let θ := fun a : ℝ => ∑' n : ℤ, g ((n:ℝ)*a)
    let σ := fun ν : ℝ => (1/2:ℂ) + ((-2*Real.pi:ℝ):ℂ)*Complex.I*(ν:ℂ)
    (∀ s : ℂ, 0 < s.re → s ≠ 1 →
      HasMellin θ s (riemannZeta s * mellin (fun a : ℝ => g a + g (-a)) s) ∧
      analyticOrderAt riemannZeta s ≤ analyticOrderAt (mellin θ) s) ∧
    ∃ T : 𝓢(ℝ,ℂ), (∀ x : ℝ, T x = (Real.exp (x/2):ℂ) * θ (Real.exp x)) ∧
      (∀ ν : ℝ, (𝓕 T) ν = mellin θ (σ ν)) ∧
      ∀ ν : ℝ, AnalyticAt ℝ (fun x : ℝ => (𝓕 T : 𝓢(ℝ,ℂ)) x) ν ∧
        analyticOrderAt riemannZeta (σ ν) ≤ analyticOrderAt (fun x : ℝ => (𝓕 T : 𝓢(ℝ,ℂ)) x) ν ∧
        ∀ j < analyticOrderNatAt riemannZeta (σ ν),
          iteratedDeriv j (fun x : ℝ => (𝓕 T : 𝓢(ℝ,ℂ)) x) ν = 0 := by
  dsimp only
  obtain ⟨hhalf,hline⟩ := rationalThetaTateHelper g hg hI
  obtain ⟨T,hT,hF⟩ := MasulloRH.thetaLogSchwartz_exists g hg hI
  exact ⟨hhalf,T,hT,hF,by rw [funext hF]; exact hline⟩
