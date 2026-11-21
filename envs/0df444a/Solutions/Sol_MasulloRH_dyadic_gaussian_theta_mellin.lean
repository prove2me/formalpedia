-- Prove2me | solution 1 for MasulloRH.dyadic_gaussian_theta_mellin
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:00:46.36287+00:00
-- url     : https://prove2.me/submissions/5132c26a-caf4-4839-ad03-d3163a640ad5

import Mathlib
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq

set_option autoImplicit false
open Filter Set MeasureTheory
open scoped Topology SchwartzMap
namespace MasulloRH
noncomputable section

private def smallConst : ℝ → ℂ := (Ioc 0 1).indicator fun _ => 1
private def largePower (a : ℂ) : ℝ → ℂ := (Ioi 1).indicator fun x => (x:ℂ)^a

private lemma largePower_hasMellin (a z : ℂ) (hz : (z+a).re < 0) :
    HasMellin (largePower a) z (-(1/(z+a))) := by
  have hpow : (z+a-1).re < -1 := by simpa [Complex.sub_re] using (show (z+a).re-1 < -1 by linarith)
  have he : ∀ x : ℝ, (x:ℂ)^(z-1) • largePower a x =
      (Ioi 1).indicator (fun t : ℝ => (t:ℂ)^(z+a-1)) x := by
    intro x
    by_cases hx : x ∈ Ioi (1:ℝ)
    · have hxn : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show 0<x by exact lt_trans zero_lt_one hx).ne'
      simp only [largePower, indicator_of_mem hx, smul_eq_mul, ← Complex.cpow_add _ _ hxn]
      congr 1
      ring
    · simp [largePower, indicator_of_notMem hx]
  have hsub : Ioi (1:ℝ) ⊆ Ioi 0 := by
    exact Set.Ioi_subset_Ioi zero_le_one
  constructor
  · simp only [MellinConvergent, he, IntegrableOn, integrable_indicator_iff measurableSet_Ioi,
      Measure.restrict_restrict_of_subset hsub]
    exact integrableOn_Ioi_cpow_of_lt hpow one_pos
  · simp only [mellin, he, integral_indicator measurableSet_Ioi, Measure.restrict_restrict_of_subset hsub]
    rw [integral_Ioi_cpow_of_lt hpow one_pos]
    simp [neg_div]

private def stripTheta (x : ℝ) : ℂ :=
  (HurwitzZeta.evenKernel 0 x : ℂ) - 1 - (x:ℂ)^(-(1/2:ℂ))

private lemma hasMellin_of_ae {f g : ℝ → ℂ} {s b : ℂ}
    (h : f =ᵐ[volume.restrict (Ioi 0)] g) (hg : HasMellin g s b) : HasMellin f s b := by
  have hh : (fun x : ℝ => (x:ℂ)^(s-1) • f x) =ᵐ[volume.restrict (Ioi 0)] fun x => (x:ℂ)^(s-1) • g x :=
    h.mono fun x hx => congrArg ((x:ℂ)^(s-1) • ·) hx
  exact ⟨hg.1.congr hh.symm, (integral_congr_ae hh).trans hg.2⟩

private lemma stripTheta_hasMellin (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    HasMellin stripTheta (s/2) (2 * completedRiemannZeta s) := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  let z := s/2
  have hz : 0 < z.re := by dsimp [z]; simpa using half_pos hs
  have hz' : (z + (-(1/2:ℂ))).re < 0 := by
    dsimp [z]; simp; linarith
  have h0 : HasMellin P.f_modif z (P.Λ₀ z) :=
    ⟨(P.isStrongFEPair_toStrongFEPair.hasMellin z).1, rfl⟩
  have hlo : HasMellin smallConst z (1/z) := hasMellin_one_Ioc hz
  have hup := largePower_hasMellin (-(1/2:ℂ)) z hz'
  have hh₁ := hasMellin_sub h0.1 hlo.1
  have hh₂ := hasMellin_sub hh₁.1 hup.1
  apply hasMellin_of_ae (g := fun x => (P.f_modif x - smallConst x) - largePower (-(1/2:ℂ)) x)
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    have hne : ∀ᵐ x : ℝ, x ≠ 1 := by
      exact compl_mem_ae_iff.mpr (measure_singleton (1:ℝ))
    filter_upwards [hne] with x hx hpos
    change 0 < x at hpos
    have hc : (↑(x ^ (-(1/2:ℝ))) : ℂ) = (x:ℂ)^(-(1/2:ℂ)) := by
      rw [Complex.ofReal_cpow hpos.le]; norm_num
    rcases lt_or_gt_of_ne hx with hlt|hgt
    · have hA : x ∈ Ioo (0:ℝ) 1 := ⟨hpos,hlt⟩
      have hB : x ∈ Ioc (0:ℝ) 1 := ⟨hpos,hlt.le⟩
      have hC : x ∉ Ioi (1:ℝ) := not_lt.mpr hlt.le
      simp only [WeakFEPair.f_modif, smallConst, largePower, stripTheta, Pi.add_apply,
        indicator_of_mem hA, indicator_of_mem hB, indicator_of_notMem hC, zero_add, sub_zero]
      change _ = ((HurwitzZeta.evenKernel 0 x : ℂ) - (1 * ((x ^ (-(1/2:ℝ)) : ℝ) : ℂ)) • (1:ℂ)) - 1
      rw [hc, smul_eq_mul, one_mul, mul_one]; ring
    · have hA : x ∉ Ioo (0:ℝ) 1 := fun hx => hgt.not_gt hx.2
      have hB : x ∉ Ioc (0:ℝ) 1 := fun hx => hgt.not_ge hx.2
      have hC : x ∈ Ioi (1:ℝ) := hgt
      simp only [WeakFEPair.f_modif, smallConst, largePower, stripTheta, Pi.add_apply,
        indicator_of_notMem hA, indicator_of_notMem hB, indicator_of_mem hC, add_zero, sub_zero]
      simp [P, HurwitzZeta.hurwitzEvenFEPair]
  · refine ⟨hh₂.1, ?_⟩
    rw [hh₂.2, hh₁.2, h0.2, hlo.2, hup.2, completedRiemannZeta_eq]
    change P.Λ₀ z - 1/z - -(1/(z + -(1/2:ℂ))) = 2 * (P.Λ₀ z / 2 - 1/s - 1/(1-s))
    dsimp [z]
    have he : s/2 + -(1/2:ℂ) = -(1-s)/2 := by ring
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_neg]
    ring

private def stripThetaSq (x : ℝ) : ℂ := stripTheta (x^2)

private lemma stripThetaSq_pos {x : ℝ} (hx : 0 < x) :
    stripThetaSq x = (HurwitzZeta.evenKernel 0 (x^2) : ℂ) - 1 - (x:ℂ)⁻¹ := by
  have hh : ((x^2:ℝ):ℂ)^(-(1/2:ℂ)) = (x:ℂ)⁻¹ := by
    have h := Complex.ofReal_cpow (sq_nonneg x) (-(1/2:ℝ))
    push_cast at h
    rw [Complex.ofReal_pow, ← h]
    have he : (x^2)^(-(1/2:ℝ)) = x⁻¹ := by
      rw [← Real.rpow_natCast_mul hx.le]; norm_num; exact Real.rpow_neg_one _
    rw [he, Complex.ofReal_inv]
  exact congrArg (fun t : ℂ => (HurwitzZeta.evenKernel 0 (x^2) : ℂ) - 1 - t) hh

private lemma stripThetaSq_hasMellin (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    HasMellin stripThetaSq s (completedRiemannZeta s) := by
  have h := stripTheta_hasMellin s hs hs'
  have h₁ := (MellinConvergent.comp_rpow (f := stripTheta) (s := s) (by norm_num : (2:ℝ) ≠ 0)).mpr (by simpa using h.1)
  have h₂ := mellin_comp_rpow stripTheta s 2
  constructor
  · change MellinConvergent (fun x : ℝ => stripTheta (x^2)) s
    simpa only [Real.rpow_two] using h₁
  · rw [show stripThetaSq = (fun x : ℝ => stripTheta (x^(2:ℝ))) by ext x; simp [stripThetaSq]]
    rw [h₂]
    push_cast
    rw [h.2]
    norm_num [Complex.real_smul]; ring

def dyadicGaussian (u : ℝ) : ℝ :=
  Real.exp (-Real.pi*u^2) - 3*Real.exp (-Real.pi*(2*u)^2) + 2*Real.exp (-Real.pi*(4*u)^2)

private def dyadicTheta (x : ℝ) : ℂ :=
  (HurwitzZeta.evenKernel 0 (x^2) : ℂ) - 3*(HurwitzZeta.evenKernel 0 ((2*x)^2) : ℂ)
      + 2*(HurwitzZeta.evenKernel 0 ((4*x)^2) : ℂ)

private lemma dyadicTheta_tsum (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℤ => (dyadicGaussian ((n:ℝ)*x) : ℂ)) (dyadicTheta x) := by
  have ht (a : ℝ) (ha : 0 < a) : HasSum (fun n : ℤ => Real.exp (-Real.pi* (a*((n:ℝ)*x))^2)) (HurwitzZeta.evenKernel 0 ((a*x)^2)) := by
    convert! HurwitzZeta.hasSum_int_evenKernel 0 (sq_pos_of_pos (mul_pos ha hx)) using 1
    funext n
    congr 1
    ring
  have hh : HasSum (fun n : ℤ => dyadicGaussian ((n:ℝ)*x))
    (HurwitzZeta.evenKernel 0 (x^2)-3*HurwitzZeta.evenKernel 0 ((2*x)^2)+2*HurwitzZeta.evenKernel 0 ((4*x)^2)) := by
      simpa [dyadicGaussian] using ((ht 1 (by norm_num)).sub ((ht 2 (by norm_num)).mul_left 3)).add ((ht 4 (by norm_num)).mul_left 2)
  simpa only [dyadicTheta, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat] using Complex.hasSum_ofReal.mpr hh

private lemma two_cpow_scale (s : ℂ) :
    (4:ℂ)^(-s) = ((2:ℂ)^(-s))^2 := by
  have h := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 2) (-s)
  norm_num at h
  simpa [sq] using h

theorem dyadicGaussian_theta_hasMellin (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    HasMellin (fun x : ℝ => ∑' n : ℤ, (dyadicGaussian ((n:ℝ)*x) : ℂ)) s
      ((1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))*completedRiemannZeta s) := by
  let R := stripThetaSq
  have hR := stripThetaSq_hasMellin s hs hs'
  have h2 := (MellinConvergent.comp_mul_left (f := R) (s := s) (by norm_num : (0:ℝ)<2)).mpr hR.1
  have h4 := (MellinConvergent.comp_mul_left (f := R) (s := s) (by norm_num : (0:ℝ)<4)).mpr hR.1
  have h3 := hasMellin_const_smul h2 (3:ℂ)
  have h5 := hasMellin_const_smul h4 (2:ℂ)
  have h₁ := hasMellin_sub hR.1 h3.1
  have h₂ := hasMellin_add h₁.1 h5.1
  apply hasMellin_of_ae (g := fun x => stripThetaSq x - (3:ℂ) • R (2*x) + (2:ℂ) • R (4*x))
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply ae_of_all
    intro x hx
    change 0 < x at hx
    dsimp only
    rw [(dyadicTheta_tsum x hx).tsum_eq]
    simp only [R, stripThetaSq_pos hx, stripThetaSq_pos (mul_pos (by norm_num : (0:ℝ)<2) hx),
      stripThetaSq_pos (mul_pos (by norm_num : (0:ℝ)<4) hx), dyadicTheta, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    simp only [mul_inv_rev]; ring
  · refine ⟨h₂.1, ?_⟩
    rw [h₂.2, h₁.2, h3.2, h5.2, hR.2, mellin_comp_mul_left _ _ (by norm_num : (0:ℝ)<2),
      mellin_comp_mul_left _ _ (by norm_num : (0:ℝ)<4)]
    simp only [R, hR.2, smul_eq_mul, Complex.ofReal_ofNat, two_cpow_scale,
      sub_eq_add_neg, Complex.cpow_add 1 (-s) (by norm_num : (2:ℂ)≠0), Complex.cpow_one]
    ring

private lemma dyadicGaussian_schwartz :
    ∃ g : 𝓢(ℝ,ℂ), ∀ x : ℝ, g x = (dyadicGaussian x : ℂ) := by
  obtain ⟨G, hG⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin 1)
  let e := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  let G₁ : 𝓢(ℝ,ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv G
  have h (x : ℝ) : G₁ x = (Real.exp (-Real.pi*x^2) : ℂ) := by
    change G (e x) = _
    calc
      G (e x) = _ := hG (e x)
      _ = ((Real.exp (-(Real.pi * ‖x‖^2))) : ℂ) :=
        congrArg (fun r : ℝ => ((Real.exp (-(Real.pi*r^2))) : ℂ)) (e.norm_map x)
      _ = _ := by simp [Real.norm_eq_abs, sq_abs]
  let d (a : ℝ) (ha : a ≠ 0) : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)
  let Ga (a : ℝ) (ha : a ≠ 0) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (d a ha) G₁
  have hGa (a : ℝ) (ha : a ≠ 0) (x : ℝ) : Ga a ha x = (Real.exp (-Real.pi*(a*x)^2) : ℂ) := by
    exact h (a*x)
  refine ⟨G₁ - (3:ℂ) • Ga 2 (by norm_num) + (2:ℂ) • Ga 4 (by norm_num), fun x => ?_⟩
  simp [h, hGa, dyadicGaussian]

private lemma dyadicGaussian_integral : (∫ x : ℝ, (dyadicGaussian x : ℂ)) = 0 := by
  let G (x : ℝ) := Real.exp (-Real.pi*x^2)
  have h : Integrable G := integrable_exp_neg_mul_sq Real.pi_pos
  have h2 := (integrable_comp_mul_left_iff G (by norm_num : (2:ℝ) ≠ 0)).mpr h
  have h4 := (integrable_comp_mul_left_iff G (by norm_num : (4:ℝ) ≠ 0)).mpr h
  have hD : (∫ x : ℝ, dyadicGaussian x) = 0 := by
    change (∫ x : ℝ, G x - 3*G (2*x) + 2*G (4*x)) = 0
    have hU : Integrable (fun x => G x - 3*G (2*x)) := h.sub (h2.const_mul 3)
    have hV : Integrable (fun x => 2*G (4*x)) := h4.const_mul 2
    rw [integral_add hU hV, integral_sub h (h2.const_mul 3),
      integral_const_mul, integral_const_mul, Measure.integral_comp_mul_left G, Measure.integral_comp_mul_left G]
    norm_num; ring
  rw [integral_complex_ofReal, hD, Complex.ofReal_zero]

private lemma dyadicFactors_ne (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    1 - (2:ℂ)^(-s) ≠ 0 ∧ 1 - (2:ℂ)^(1-s) ≠ 0 := by
  have h₁ : ‖(2:ℂ)^(-s)‖ < 1 := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by simpa using hs)
  have h₂ : 1 < ‖(2:ℂ)^(1-s)‖ := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    exact Real.one_lt_rpow (by norm_num) (by simpa using hs')
  constructor
  · intro h; rw [← sub_eq_zero.mp h, norm_one] at h₁; exact lt_irrefl _ h₁
  · intro h; rw [← sub_eq_zero.mp h, norm_one] at h₂; exact lt_irrefl _ h₂

private lemma dyadicGaussian_order (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    AnalyticAt ℂ (mellin (fun x : ℝ => ∑' n : ℤ, (dyadicGaussian ((n:ℝ)*x) : ℂ))) s ∧
    analyticOrderAt (mellin (fun x : ℝ => ∑' n : ℤ, (dyadicGaussian ((n:ℝ)*x) : ℂ))) s =
      analyticOrderAt riemannZeta s := by
  let A (z : ℂ) := (1-(2:ℂ)^(-z))*(1-(2:ℂ)^(1-z))*Complex.Gammaℝ z
  have hunit : A s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (dyadicFactors_ne s hs hs').1 (dyadicFactors_ne s hs hs').2)
      (Complex.Gammaℝ_ne_zero_of_re_pos hs)
  have hΓinv := Complex.differentiable_Gammaℝ_inv.analyticAt s
  have hΓ : AnalyticAt ℂ Complex.Gammaℝ s := by
    have h := hΓinv.inv (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs))
    change AnalyticAt ℂ (fun z => ((Complex.Gammaℝ z)⁻¹)⁻¹) s at h
    simpa only [inv_inv] using h
  have hA : AnalyticAt ℂ A s := by
    apply AnalyticAt.mul _ hΓ
    apply Differentiable.analyticAt
    fun_prop (disch := norm_num)
  have hζ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by
    change s ≠ 1
    intro h; simp [h] at hs')
  have he : mellin (fun x : ℝ => ∑' n : ℤ, (dyadicGaussian ((n:ℝ)*x) : ℂ)) =ᶠ[𝓝 s] (A*riemannZeta) := by
    have hpos : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    have hlt : ∀ᶠ z : ℂ in 𝓝 s, z.re < 1 := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hs'
    filter_upwards [hpos, hlt] with z hz hz'
    change _ = A z * riemannZeta z
    rw [(dyadicGaussian_theta_hasMellin z hz hz').2, riemannZeta_def_of_ne_zero (by intro h; simp [h] at hz)]
    dsimp [A]
    field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hz]
  refine ⟨(hA.mul hζ).congr he.symm, ?_⟩
  rw [analyticOrderAt_congr he, analyticOrderAt_mul hA hζ, hA.analyticOrderAt_eq_zero.mpr hunit, zero_add]

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

private lemma dyadicGaussian_realOrder (ν : ℝ) :
    let σ (x : ℝ) : ℂ := 1/2+((-2*Real.pi : ℝ):ℂ)*Complex.I*(x:ℂ)
    analyticOrderAt (fun x : ℝ => mellin (fun y : ℝ => ∑' n : ℤ, (dyadicGaussian ((n:ℝ)*y) : ℂ)) (σ x)) ν =
      analyticOrderAt riemannZeta (σ ν) := by
  dsimp only
  let a : ℂ := 1/2
  let b : ℂ := ((-2*Real.pi : ℝ):ℂ)*Complex.I
  have hb : b ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero
  have hz : (a+b*(ν:ℂ)).re = 1/2 := by simp [a,b, Complex.mul_re, Complex.mul_im]
  have h := dyadicGaussian_order (a+b*(ν:ℂ)) (by rw [hz]; norm_num) (by rw [hz]; norm_num)
  exact (real_affine_order _ a b hb ν h.1).trans h.2

end
end MasulloRH

open MasulloRH
open scoped SchwartzMap

/-- An explicit admissible Schwartz generator of the rational theta image detects the
zeros of the Riemann zeta function throughout the open critical strip. -/
theorem solution :
    ∃ g : 𝓢(ℝ,ℂ),
      (∀ x : ℝ, g x = ((Real.exp (-Real.pi*x^2) - 3*Real.exp (-Real.pi*(2*x)^2)
        + 2*Real.exp (-Real.pi*(4*x)^2) : ℝ) : ℂ)) ∧
      g 0 = 0 ∧ (∫ x : ℝ, g x) = 0 ∧
      (∀ s : ℂ, 0 < s.re → s.re < 1 →
        HasMellin (fun x : ℝ => ∑' n : ℤ, g ((n:ℝ)*x)) s
          ((1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))*completedRiemannZeta s) ∧
        (mellin (fun x : ℝ => ∑' n : ℤ, g ((n:ℝ)*x)) s = 0 ↔ riemannZeta s = 0) ∧
        analyticOrderAt (mellin (fun x : ℝ => ∑' n : ℤ, g ((n:ℝ)*x))) s = analyticOrderAt riemannZeta s) ∧
      ∀ ν : ℝ, let σ (x : ℝ) : ℂ := 1/2+((-2*Real.pi : ℝ):ℂ)*Complex.I*(x:ℂ)
        analyticOrderAt (fun x : ℝ => mellin (fun y : ℝ => ∑' n : ℤ, g ((n:ℝ)*y)) (σ x)) ν =
          analyticOrderAt riemannZeta (σ ν) := by
  obtain ⟨g, hg⟩ := dyadicGaussian_schwartz
  refine ⟨g, hg, by norm_num [hg, dyadicGaussian], ?_, ?_, ?_⟩
  · simpa only [hg] using dyadicGaussian_integral
  · intro s hs hs'
    have hm := dyadicGaussian_theta_hasMellin s hs hs'
    have hd := dyadicFactors_ne s hs hs'
    have hz : s ≠ 0 := by intro h; simp [h] at hs
    simp only [hg]
    refine ⟨hm, ?_, (dyadicGaussian_order s hs hs').2⟩
    rw [hm.2, riemannZeta_def_of_ne_zero hz]
    simp only [mul_eq_zero, hd.1, hd.2, false_or, div_eq_zero_iff, Complex.Gammaℝ_ne_zero_of_re_pos hs, or_false]
  · intro ν
    simpa only [hg] using dyadicGaussian_realOrder ν
