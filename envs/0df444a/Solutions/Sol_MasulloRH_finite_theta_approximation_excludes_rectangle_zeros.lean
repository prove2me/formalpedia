-- Prove2me | solution 1 for MasulloRH.finite_theta_approximation_excludes_rectangle_zeros
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:02:54.022668+00:00
-- url     : https://prove2.me/submissions/5b2cbfbc-22d8-4073-bb0e-dbecd2699cb3

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib
import Theorems.Thm_MasulloAudit_window_mellin_evaluation_bounded
import Theorems.Thm_MasulloRH_dyadic_gaussian_theta_mellin
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

section

namespace MasulloGram.ThetaEstimates
section
open Set Filter MeasureTheory Asymptotics
open scoped Topology SchwartzMap FourierTransform
namespace MasulloRH
noncomputable section

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
end
section
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
end
end MasulloSynthesis
end
end MasulloGram.ThetaEstimates


open MeasureTheory Set Filter FourierTransform
open scoped SchwartzMap FourierTransform Topology
namespace MasulloGram
noncomputable section

def theta (x : ℝ) : ℂ := ∑' k : ℤ,
  let t := (k:ℝ) * Real.exp x
  ((Real.exp (-Real.pi*t^2) - 3*Real.exp (-Real.pi*(2*t)^2) +
    2*Real.exp (-Real.pi*(4*t)^2) : ℝ) : ℂ)

private lemma hasMellin_log_iff (F : ℝ → ℂ) (s r : ℂ) :
    HasMellin F s r ↔ Integrable (fun x : ℝ => Complex.exp (s*x) * F (Real.exp x)) ∧
      (∫ x : ℝ, Complex.exp (s*x) * F (Real.exp x)) = r := by
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have him : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have he (x : ℝ) : |Real.exp x| • (((Real.exp x : ℝ):ℂ)^(s-1) • F (Real.exp x)) =
      Complex.exp (s*x)*F (Real.exp x) := by
    rw [abs_of_pos (Real.exp_pos _),Complex.real_smul,smul_eq_mul,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp,Complex.ofReal_exp,←mul_assoc,←Complex.exp_add]
    congr 2; ring
  unfold HasMellin MellinConvergent mellin
  rw [← him,integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn]
  simp only [integrableOn_univ, setIntegral_univ, he]

theorem theta_continuous : Continuous theta := by
  obtain ⟨g,hg,h0,_,_,_⟩ := MasulloRH.dyadic_gaussian_theta_mellin
  let f := ThetaEstimates.MasulloRH.thetaNat (g + ThetaEstimates.MasulloRH.reflectS g)
  have he : theta = f ∘ Real.exp := by
    funext x
    change theta x = ThetaEstimates.MasulloRH.thetaNat _ _
    rw [← ThetaEstimates.MasulloRH.theta_split g h0 (Real.exp_pos x)]
    simp only [ThetaEstimates.MasulloRH.theta,theta,hg]
  rw [he]
  exact (ThetaEstimates.MasulloRH.thetaNat_continuousOn _).comp_continuous Real.continuous_exp Real.exp_pos

theorem theta_measurable : Measurable theta := theta_continuous.measurable

private theorem theta_bounds : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ x : ℝ,
    ‖theta x‖ ≤ A*Real.exp (-2*x) ∧ ‖theta x‖ ≤ B*Real.exp x := by
  obtain ⟨g,hg,h0,hI,_,_⟩ := MasulloRH.dyadic_gaussian_theta_mellin
  have hF : (𝓕 g : 𝓢(ℝ,ℂ)) 0=0 := by
    change 𝓕 (⇑g) 0=0
    simpa [Real.fourier_real_eq_integral_exp_smul] using hI
  obtain ⟨A,hA,ha⟩ := ThetaEstimates.MasulloRH.thetaSchwartz_bound g h0 2 (by decide)
  obtain ⟨B,hB,hb⟩ := ThetaEstimates.MasulloRH.thetaSchwartz_bound (𝓕 g) hF 2 (by decide)
  refine ⟨A,B,hA,hB,fun x => ?_⟩
  have he : theta x = ∑' n : ℤ, g ((n:ℝ)*Real.exp x) := by simp only [theta,hg]
  rw [he]
  constructor
  · apply (ha _ (Real.exp_pos x)).trans_eq
    rw [←Real.exp_nat_mul,←Real.exp_neg]
    push_cast
    ring_nf
  · rw [ThetaEstimates.MasulloSynthesis.theta_poisson_scaled g (Real.exp_pos x),norm_smul,
      Real.norm_of_nonneg (inv_pos.mpr (Real.exp_pos x)).le]
    apply (mul_le_mul_of_nonneg_left (hb _ (inv_pos.mpr (Real.exp_pos x)))
      (inv_pos.mpr (Real.exp_pos x)).le).trans_eq
    field_simp

theorem theta_shift_zero_integral (s : ℂ) (y : ℝ) (hs0 : 0<s.re) (hs1 : s.re<1)
    (hz : riemannZeta s = 0) :
    Integrable (fun x : ℝ => Complex.exp (s*x) * theta (x-y)) ∧
      (∫ x : ℝ, Complex.exp (s*x) * theta (x-y)) = 0 := by
  obtain ⟨g,hg,_,_,hm,_⟩ := MasulloRH.dyadic_gaussian_theta_mellin
  let F (t : ℝ) := ∑' k : ℤ, g ((k:ℝ)*t)
  have ht : HasMellin F s 0 := ⟨(hm s hs0 hs1).1.1,(hm s hs0 hs1).2.1.mpr hz⟩
  obtain ⟨hi,hM⟩ := (hasMellin_log_iff F s 0).1 ht
  have he (t : ℝ) : F (Real.exp t) = theta t := by simp only [F,theta,hg]
  simp only [he] at hi hM
  let H (x : ℝ) := Complex.exp (s*x)*theta x
  have h (x : ℝ) : Complex.exp (s*x)*theta (x-y) = Complex.exp (s*y)*H (x-y) := by
    dsimp [H]
    rw [←mul_assoc,←Complex.exp_add]
    push_cast
    congr 2
    ring
  simp_rw [h]
  refine ⟨(hi.comp_sub_right y).const_mul _,?_⟩
  rw [integral_const_mul,integral_sub_right_eq_self,hM,mul_zero]

theorem theta_shift_energy (c b y : ℝ) (hlo : 0<c-b) (hhi : c+b<1) :
    Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|) * ‖theta (x-y)‖^2) := by
  obtain ⟨A,B,hA,hB,h⟩ := theta_bounds
  obtain ⟨hi,_,_⟩ := MasulloAudit.window_mellin_evaluation_bounded 1 (by norm_num) 0 (by norm_num)
  norm_num at hi
  have hi' : Integrable (fun x : ℝ => Real.exp (-2*|x|)) := by simpa only [neg_mul] using hi
  let M := A^2*Real.exp (4*y) + B^2*Real.exp (-2*y)
  have hcont : Continuous (fun x : ℝ => Real.exp (2*c*x+2*b*|x|) * ‖theta (x-y)‖^2) :=
    (Real.continuous_exp.comp (by fun_prop)).mul ((theta_continuous.comp (continuous_id.sub continuous_const)).norm.pow 2)
  apply (hi'.const_mul M).mono' hcont.aestronglyMeasurable
  refine ae_of_all _ fun x => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
  have hrewrite (u K v : ℝ) : Real.exp u*(K*Real.exp v)^2 = K^2*Real.exp (u+2*v) := by
    rw [Real.exp_add,two_mul v,Real.exp_add]; ring
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    calc
      _ ≤ Real.exp (2*c*x+2*b*x)*(A*Real.exp (-2*(x-y)))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h (x-y)).1 2) (Real.exp_nonneg _)
      _ = _ := hrewrite _ _ _
      _ ≤ A^2*Real.exp (4*y+(-2*x)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (sq_nonneg _)
        nlinarith [mul_nonneg (sub_nonneg.mpr hhi.le) hx]
      _ ≤ M*Real.exp (-2*x) := by
        rw [Real.exp_add,←mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (Real.exp_nonneg _)
  · rw [abs_of_neg (lt_of_not_ge hx)]
    calc
      _ ≤ Real.exp (2*c*x+2*b* -x)*(B*Real.exp (x-y))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h (x-y)).2 2) (Real.exp_nonneg _)
      _ = _ := hrewrite _ _ _
      _ ≤ B^2*Real.exp (-2*y+(-2* -x)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (sq_nonneg _)
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hlo.le (le_of_not_ge hx)]
      _ ≤ M*Real.exp (-2* -x) := by
        rw [Real.exp_add,←mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (Real.exp_nonneg _)

end
end MasulloGram

end

section

open MeasureTheory Set

noncomputable section
namespace MasulloGram

def pulse (T x : ℝ) : ℂ := (((T+1)/Real.sqrt Real.pi : ℝ):ℂ) *
    Complex.exp (-(((T+1)*x : ℝ):ℂ)^2)

def pulseValue (T : ℝ) (s : ℂ) : ℂ := Complex.exp (s^2/(4*((T+1:ℝ):ℂ)^2))

private lemma pulse_laplace_form (T : ℝ) (s : ℂ) (x : ℝ) :
    Complex.exp (s*x) * pulse T x = (((T+1)/Real.sqrt Real.pi : ℝ):ℂ) *
      Complex.exp (-(((T+1)^2 : ℝ):ℂ)*x^2 + s*x + 0) := by
  unfold pulse
  rw [add_zero, Complex.exp_add]
  push_cast
  ring_nf

lemma pulse_laplace_integrable {T : ℝ} (hT : 0 ≤ T) (s : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (s*x) * pulse T x) := by
  simp_rw [pulse_laplace_form]
  exact (integrable_cexp_quadratic (b:=(((T+1)^2:ℝ):ℂ)) (by norm_cast; positivity) s 0).const_mul _

private lemma normalizing_root {a : ℝ} (ha : 0 < a) :
    (((Real.pi/a^2:ℝ):ℂ) ^ (1/2:ℂ)) = ((Real.sqrt Real.pi/a : ℝ):ℂ) := by
  have hr : (((1/2:ℝ):ℂ)) = (1/2:ℂ) := by norm_num
  rw [← hr, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow,
    Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq ha.le]

lemma pulse_laplace {T : ℝ} (hT : 0 ≤ T) (s : ℂ) :
    (∫ x : ℝ, Complex.exp (s*x) * pulse T x) = pulseValue T s := by
  simp_rw [pulse_laplace_form]
  rw [integral_const_mul, integral_cexp_quadratic (show (-(((T+1)^2 : ℝ):ℂ)).re < 0 by
    simp only [Complex.neg_re, Complex.ofReal_re]; nlinarith), neg_neg]
  rw [← Complex.ofReal_div, normalizing_root (show 0 < T+1 by linarith), ← mul_assoc,
    ← Complex.ofReal_mul]
  have hr : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have ha : T+1 ≠ 0 := by linarith
  rw [show (T+1)/Real.sqrt Real.pi*(Real.sqrt Real.pi/(T+1))=1 by field_simp,
    Complex.ofReal_one, one_mul]
  unfold pulseValue
  congr 1
  rw [zero_sub, mul_neg, div_neg, neg_neg, Complex.ofReal_pow]

lemma le_norm_pulseValue {T : ℝ} (hT : 0 ≤ T) {s : ℂ} (hs : |s.im| ≤ T) :
    Real.exp (-(1/4:ℝ)) ≤ ‖pulseValue T s‖ := by
  rw [pulseValue, Complex.norm_exp, Real.exp_le_exp]
  have ha : 0 < 4*(T+1)^2 := by positivity
  have he : (4:ℂ)*((T+1:ℝ):ℂ)^2 = ((4*(T+1)^2:ℝ):ℂ) := by push_cast; rfl
  rw [he, Complex.div_ofReal_re, le_div_iff₀ ha, pow_two s, Complex.mul_re]
  have hsq := mul_self_le_mul_self (abs_nonneg s.im) hs
  rw [← sq, sq_abs] at hsq
  nlinarith [sq_nonneg s.re]

private lemma real_gaussian_linear_integrable {k : ℝ} (hk : 0 < k) (v : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-k*x^2+v*x)) := by
  have h := (integrable_cexp_quadratic (b := (k:ℂ)) (by exact hk) (v:ℂ) 0).norm
  convert! h using 1
  try rfl
  funext x
  rw [Complex.norm_exp, add_zero, ← Complex.ofReal_pow]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_im, Complex.ofReal_re, Complex.neg_im, neg_zero, mul_zero, sub_zero]

lemma pulse_weighted_integrable {T : ℝ} (hT : 0 ≤ T) (c b : ℝ) :
    Integrable (fun x : ℝ => ‖pulse T x‖^2 * Real.exp (2*c*x+2*b*|x|)) := by
  let k := 2*(T+1)^2
  have hk : 0 < k := by dsimp [k]; positivity
  let u : ℝ := ((T+1)/Real.sqrt Real.pi)^2
  have hL := (real_gaussian_linear_integrable hk (2*c+2*b)).const_mul u
  have hR := (real_gaussian_linear_integrable hk (2*c-2*b)).const_mul u
  have h := Integrable.piecewise (s := Ici (0:ℝ)) measurableSet_Ici hL.integrableOn hR.integrableOn
  convert! h using 1
  try rfl
  funext x
  have ha : 0 ≤ (T+1)/Real.sqrt Real.pi := by positivity
  rw [pulse, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
    ← Complex.ofReal_pow, Complex.neg_re, Complex.ofReal_re, mul_pow, ← Real.exp_nat_mul, mul_assoc,
    ← Real.exp_add]
  by_cases hx : 0 ≤ x
  · rw [piecewise_eq_of_mem _ _ _ (show x∈Ici 0 from hx), abs_of_nonneg hx]
    dsimp [k,u]; congr 2; ring
  · rw [piecewise_eq_of_notMem _ _ _ (show x∉Ici 0 from hx), abs_of_neg (lt_of_not_ge hx)]
    dsimp [k,u]; congr 2; ring

end MasulloGram

end

end

section
open MeasureTheory
open scoped ComplexConjugate BigOperators
namespace MasulloGram
noncomputable section

/-- The positive weight used to control Laplace evaluation in the open strip. -/
def gramWeight (c b x : ℝ) := Real.exp (2*c*x+2*b*|x|)

def gramEntry (c b : ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, (gramWeight c b x : ℂ) * conj (f x) * g x

theorem gramEntry_integrable (c b : ℝ) {f g : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hF : Integrable (fun x => gramWeight c b x * ‖f x‖^2))
    (hG : Integrable (fun x => gramWeight c b x * ‖g x‖^2)) :
    Integrable (fun x : ℝ => (gramWeight c b x : ℂ)*conj (f x)*g x) := by
  apply ((hF.add hG).const_mul (1/2:ℝ)).mono'
  · exact ((show Continuous (fun x : ℝ => (gramWeight c b x : ℂ)) by unfold gramWeight; fun_prop).aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hf)).mul hg
  · apply Filter.Eventually.of_forall
    intro x
    have hw : 0 ≤ gramWeight c b x := (Real.exp_pos _).le
    simp only [norm_mul, Complex.norm_conj,Complex.norm_real,Real.norm_of_nonneg hw,Pi.add_apply]
    nlinarith [mul_nonneg hw (sq_nonneg (‖f x‖-‖g x‖))]

theorem gramEntry_conj (c b : ℝ) (f g : ℝ→ℂ) :
    conj (gramEntry c b f g) = gramEntry c b g f := by
  unfold gramEntry
  rw [← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp [mul_assoc,mul_comm]

private theorem gram_pointwise {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ℂ) (a u : ι → ℂ) (b v : κ → ℂ) :
    w * conj (∑ i, a i*u i) * (∑ j, b j*v j) =
      ∑ i, ∑ j, (conj (a i)*b j) * (w*conj (u i)*v j) := by
  calc
    _ = (∑ i, w*(conj (a i)*conj (u i))) * (∑ j, b j*v j) := by
      congr 1
      rw [map_sum, Finset.mul_sum]
      simp only [map_mul]
    _ = ∑ i, (w*(conj (a i)*conj (u i))) * (∑ j, b j*v j) := Finset.sum_mul ..
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Hermitian inner product of finite linear combinations is the corresponding matrix form. -/
theorem gramEntry_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c b : ℝ) (f : ι → ℝ → ℂ) (g : κ → ℝ → ℂ) (a : ι→ℂ) (d : κ→ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) volume) (hg : ∀ j, AEStronglyMeasurable (g j) volume)
    (hF : ∀ i, Integrable (fun x => gramWeight c b x * ‖f i x‖^2))
    (hG : ∀ j, Integrable (fun x => gramWeight c b x * ‖g j x‖^2)) :
    Integrable (fun x : ℝ => (gramWeight c b x:ℂ) * conj (∑ i, a i*f i x) * (∑ j, d j*g j x)) ∧
    gramEntry c b (fun x => ∑ i, a i*f i x) (fun x => ∑ j, d j*g j x) =
      ∑ i, ∑ j, conj (a i)*d j*gramEntry c b (f i) (g j) := by
  let K (i : ι) (j : κ) (x : ℝ) := (conj (a i)*d j)*((gramWeight c b x:ℂ)*conj (f i x)*g j x)
  have hK (i j) : Integrable (K i j) :=
    (gramEntry_integrable c b (hf i) (hg j) (hF i) (hG j)).const_mul _
  have he (x : ℝ) : (gramWeight c b x:ℂ)*conj (∑ i, a i*f i x)*(∑ j, d j*g j x) =
      ∑ i, ∑ j, K i j x := gram_pointwise _ _ _ _ _
  have hrow (i) : Integrable (fun x => ∑ j, K i j x) := integrable_finsetSum _ (fun j _ => hK i j)
  constructor
  · simp only [he]
    exact integrable_finsetSum _ (fun i _ => hrow i)
  · unfold gramEntry
    simp only [he]
    rw [integral_finsetSum _ (fun i _ => hrow i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hK i j)]
    exact Finset.sum_congr rfl (fun j _ => integral_const_mul ..)

/-- Weighted Gram energy is the real part of the Hermitian quadratic form. -/
theorem finite_gram_energy {ι : Type*} [Fintype ι] (c b : ℝ) (f : ι→ℝ→ℂ) (a : ι→ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) volume)
    (hF : ∀ i, Integrable (fun x => gramWeight c b x * ‖f i x‖^2)) :
    AEStronglyMeasurable (fun x => ∑ i, a i*f i x) volume ∧
      Integrable (fun x : ℝ => gramWeight c b x * ‖∑ i, a i*f i x‖^2) ∧
      (∫ x : ℝ, gramWeight c b x * ‖∑ i, a i*f i x‖^2) =
        (∑ i, ∑ j, conj (a i)*a j*gramEntry c b (f i) (f j)).re := by
  obtain ⟨hint,hid⟩ := gramEntry_sum_sum c b f f a a hf hf hF hF
  let S (x : ℝ) := ∑ i, a i*f i x
  have he (x : ℝ) : ((gramWeight c b x:ℂ)*conj (S x)*S x).re = gramWeight c b x * ‖S x‖^2 := by
    rw [mul_assoc,Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hint' : Integrable (fun x : ℝ => gramWeight c b x * ‖S x‖^2) := by
    have hreal : Integrable (fun x : ℝ => ((gramWeight c b x:ℂ)*conj (S x)*S x).re) := hint.re
    simpa only [he] using hreal
  refine ⟨Finset.aestronglyMeasurable_fun_sum _ (fun i _ => aestronglyMeasurable_const.mul (hf i)),hint',?_⟩
  rw [← hid]
  change (∫ x : ℝ, gramWeight c b x * ‖S x‖^2) = (∫ x : ℝ, (gramWeight c b x:ℂ)*conj (S x)*S x).re
  have hir : (∫ x : ℝ, ((gramWeight c b x:ℂ)*conj (S x)*S x).re) =
      (∫ x : ℝ, (gramWeight c b x:ℂ)*conj (S x)*S x).re := integral_re hint
  simpa only [he] using hir

/-- Signed residual form. Index zero is the target, and the remaining entries are the trial
columns. Its quadratic form, including all cross terms, is the exact residual energy. -/
theorem finite_gram_residual {m : ℕ} (c b : ℝ) (h : ℝ→ℂ) (f : Fin m→ℝ→ℂ) (a : Fin m→ℂ)
    (hh : AEStronglyMeasurable h volume) (hf : ∀ i, AEStronglyMeasurable (f i) volume)
    (hH : Integrable (fun x => gramWeight c b x * ‖h x‖^2))
    (hF : ∀ i, Integrable (fun x => gramWeight c b x * ‖f i x‖^2)) :
    let v := Fin.cons h f
    let d := Fin.cons (1:ℂ) (fun j => -a j)
    AEStronglyMeasurable (fun x => h x - ∑ j, a j*f j x) volume ∧
      Integrable (fun x : ℝ => gramWeight c b x * ‖h x - ∑ j, a j*f j x‖^2) ∧
      (∫ x : ℝ, gramWeight c b x * ‖h x - ∑ j, a j*f j x‖^2) =
        (∑ i, ∑ j, conj (d i)*d j*gramEntry c b (v i) (v j)).re := by
  intro v d
  have hv (i : Fin (m+1)) : AEStronglyMeasurable (v i) volume := Fin.cases hh hf i
  have hV (i : Fin (m+1)) : Integrable (fun x => gramWeight c b x * ‖v i x‖^2) := Fin.cases hH hF i
  have hs (x : ℝ) : ∑ i, d i*v i x = h x - ∑ j, a j*f j x := by
    simp [v,d,Fin.sum_univ_succ,Finset.sum_neg_distrib,sub_eq_add_neg]
  simpa only [hs] using finite_gram_energy c b v d hv hV

end
end MasulloGram

end

section

open MeasureTheory Set Filter
open scoped Topology
namespace MasulloGram

/-- The Laplace transform of a finite-energy residual is absolutely convergent throughout
the inner rectangle, with a uniform point-evaluation constant determined by its margin. -/
theorem laplace_bound (q : ℝ → ℂ) (hq : AEStronglyMeasurable q volume)
    (c b δ : ℝ) (hδ : 0 < δ) (s : ℂ) (hs : |s.re-c| ≤ b-δ)
    (hJ : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖q x‖^2)) :
    Integrable (fun x : ℝ => Complex.exp (s*(x:ℂ))*q x) ∧
      ‖∫ x : ℝ, Complex.exp (s*(x:ℂ))*q x‖^2 ≤
        (∫ x : ℝ, Real.exp (2*c*x+2*b*|x|)*‖q x‖^2)/δ := by
  let A (x : ℝ) := Real.exp (c*x+b*|x|)*‖q x‖
  let B (x : ℝ) := Real.exp ((s.re-c)*x-b*|x|)
  let J := ∫ x : ℝ, Real.exp (2*c*x+2*b*|x|)*‖q x‖^2
  have hA2 (x : ℝ) : A x^2 = Real.exp (2*c*x+2*b*|x|)*‖q x‖^2 := by
    simp only [A,mul_pow,← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hB2 (x : ℝ) : B x^2 = Real.exp (2*(s.re-c)*x-2*b*|x|) := by
    dsimp only [B]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hAmeas : AEStronglyMeasurable A volume :=
    (show Continuous (fun x : ℝ => Real.exp (c*x+b*|x|)) by fun_prop).aestronglyMeasurable.mul hq.norm
  have hA : MemLp A 2 volume := (memLp_two_iff_integrable_sq hAmeas).mpr (by simpa only [hA2] using hJ)
  have hba : |s.re-c| < b := by linarith
  have hb : 0 < b := lt_of_le_of_lt (abs_nonneg _) hba
  have hz : (s-(c:ℂ)).re = s.re-c := by simp
  obtain ⟨hK,hKint,_,_⟩ := MasulloAudit.window_mellin_evaluation_bounded b hb (s-(c:ℂ)) (hz ▸ hba)
  rw [hz] at hK hKint
  have hB : MemLp B 2 volume := (memLp_two_iff_integrable_sq (by dsimp [B]; fun_prop)).mpr (by
    simpa only [hB2] using hK)
  have hAB := hA.integrable_mul hB
  have hnorm (x : ℝ) : ‖Complex.exp (s*(x:ℂ))*q x‖ = A x * B x := by
    simp only [A,B,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    calc
      _ = (Real.exp (c*x+b*|x|)*Real.exp ((s.re-c)*x-b*|x|)) * ‖q x‖ := by
        rw [← Real.exp_add]; congr 2; ring
      _ = _ := by ring
  refine ⟨hAB.mono' ((show Continuous (fun x : ℝ => Complex.exp (s*(x:ℂ))) by fun_prop).aestronglyMeasurable.mul hq)
    (Eventually.of_forall fun x => (hnorm x).le),?_⟩
  let C := 1 / (2*(b-(s.re-c))) + 1 / (2*(b+(s.re-c)))
  have hJ0 : 0 ≤ J := integral_nonneg (fun x => by positivity)
  have hpm := abs_le.mp hs
  have hm : δ ≤ b-(s.re-c) := by linarith
  have hp : δ ≤ b+(s.re-c) := by linarith
  have hm0 := hδ.trans_le hm
  have hp0 := hδ.trans_le hp
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hC : C ≤ 1/δ := by
    apply (add_le_add (one_div_le_one_div_of_le (show 0<2*δ by positivity) (by linarith : 2*δ ≤ 2*(b-(s.re-c))))
      (one_div_le_one_div_of_le (show 0<2*δ by positivity) (by linarith : 2*δ ≤ 2*(b+(s.re-c))))).trans_eq
    field_simp
    ring
  have hho := integral_mul_le_Lp_mul_Lq_of_nonneg (μ:=volume) (p:=2) (q:=2) (by norm_num [Real.holderConjugate_iff])
    (f:=A) (g:=B) (Eventually.of_forall fun x => mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
    (Eventually.of_forall fun x => Real.exp_nonneg _) (by simpa using hA) (by simpa using hB)
  have hI : ‖∫ x : ℝ, Complex.exp (s*(x:ℂ))*q x‖ ≤ Real.sqrt J * Real.sqrt C := by
    apply (norm_integral_le_integral_norm _).trans
    simp only [hnorm]
    simpa only [Real.rpow_two,hA2,hB2,hKint,← Real.sqrt_eq_rpow,J,C] using hho
  calc
    _ ≤ (Real.sqrt J * Real.sqrt C)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hI
    _ = J*C := by rw [mul_pow,Real.sq_sqrt hJ0,Real.sq_sqrt hC0]
    _ ≤ J/δ := by simpa only [div_eq_mul_inv,one_mul] using (mul_le_mul_of_nonneg_left hC hJ0)

end MasulloGram

end

section

open MeasureTheory
open scoped BigOperators
namespace MasulloGram

private theorem sum_eval_zero {m : ℕ} (p : ℝ → ℂ) (F : Fin m → ℝ → ℂ) (a : Fin m → ℂ)
    (s : ℂ) (hp : Integrable (fun x : ℝ => Complex.exp (s*x)*p x))
    (hF : ∀ i, Integrable (fun x : ℝ => Complex.exp (s*x)*F i x) ∧
      (∫ x : ℝ, Complex.exp (s*x)*F i x) = 0) :
    (∫ x : ℝ, Complex.exp (s*x) * (p x-∑ i, a i*F i x)) =
      ∫ x : ℝ, Complex.exp (s*x)*p x := by
  have hi (i : Fin m) : Integrable (fun x : ℝ => a i*(Complex.exp (s*x)*F i x)) :=
    (hF i).1.const_mul _
  have he (x : ℝ) : Complex.exp (s*x) * (p x-∑ i, a i*F i x) =
      Complex.exp (s*x)*p x - ∑ i, a i*(Complex.exp (s*x)*F i x) := by
    rw [mul_sub,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_sub hp (integrable_finsetSum _ (fun i _ => hi i)), integral_finsetSum _ (fun i _ => hi i)]
  simp only [integral_const_mul,(hF _).2,mul_zero,Finset.sum_const_zero,sub_zero]

theorem excludes_at_zero {m : ℕ} (T c b δ : ℝ) (hT : 0≤T) (hδ : 0<δ)
    (s : ℂ) (hs : |s.re-c| ≤ b-δ) (ht : |s.im|≤T)
    (f : Fin m → ℝ → ℂ) (a : Fin m → ℂ)
    (hf : ∀ i, Integrable (fun x : ℝ => Complex.exp (s*x)*f i x) ∧
      (∫ x : ℝ, Complex.exp (s*x)*f i x) = 0)
    (q : ℝ → ℂ) (hq : ∀ x, q x = pulse T x - ∑ i, a i*f i x)
    (hm : AEStronglyMeasurable q volume)
    (hi : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖q x‖^2)) :
    δ*Real.exp (-(1/2:ℝ)) ≤ ∫ x : ℝ, Real.exp (2*c*x+2*b*|x|)*‖q x‖^2 := by
  have h := (laplace_bound q hm c b δ hδ s hs hi).2
  have he : (∫ x : ℝ, Complex.exp (s*x)*q x) = pulseValue T s := by
    simp_rw [hq]
    rw [sum_eval_zero _ _ _ _ (pulse_laplace_integrable hT s) hf,pulse_laplace hT s]
  rw [he] at h
  have hl := le_norm_pulseValue hT ht
  have hsquare := pow_le_pow_left₀ (Real.exp_pos _).le hl 2
  rw [←Real.exp_nat_mul] at hsquare
  norm_num at hsquare
  have hlow : Real.exp (-(1/2:ℝ)) ≤ ‖pulseValue T s‖ ^ 2 := by exact hsquare
  simpa only [mul_comm δ] using (le_div_iff₀ hδ).mp (hlow.trans h)

end MasulloGram

end

section

open MeasureTheory MasulloRH.GaussianApproximation
open scoped BigOperators ComplexConjugate

theorem MasulloGram.rectangle {m : ℕ} (T c b δ : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hδ : 0 < δ) (hlo : 0 < c-b) (hhi : c+b < 1) :
    let u : Fin (m+1) → ℝ → ℂ := Fin.cons (MasulloRH.GaussianApproximation.pulse T)
      (fun i : Fin m => fun x : ℝ => MasulloRH.GaussianApproximation.theta (x-y i))
    let d : Fin (m+1) → ℂ := Fin.cons (1:ℂ) (fun i : Fin m => -a i)
    Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖residual T a y x‖^2) ∧
      (∀ i j : Fin (m+1), Integrable (fun x : ℝ => (Real.exp (2*c*x+2*b*|x|):ℂ) *
        conj (u i x) * u j x)) ∧
      energy c b (residual T a y) = (∑ i, ∑ j, conj (d i)*d j *
        ∫ x : ℝ, (Real.exp (2*c*x+2*b*|x|):ℂ)*conj (u i x)*u j x).re ∧
      (∀ s : ℂ, |s.re-c| ≤ b-δ → |s.im| ≤ T → riemannZeta s = 0 →
        δ*Real.exp (-(1/2:ℝ)) ≤ energy c b (residual T a y)) := by
  classical
  intro u d
  let f (i : Fin m) (x : ℝ) := theta (x-y i)
  have hh : Continuous (pulse T) := by unfold pulse; fun_prop
  have hf (i : Fin m) : Continuous (f i) := theta_continuous.comp (continuous_id.sub continuous_const)
  have hH : Integrable (fun x => gramWeight c b x*‖pulse T x‖^2) := by
    simpa only [gramWeight,mul_comm (Real.exp _)] using pulse_weighted_integrable hT c b
  have hF (i : Fin m) : Integrable (fun x => gramWeight c b x*‖f i x‖^2) :=
    theta_shift_energy c b (y i) hlo hhi
  obtain ⟨hm,hi,hG⟩ := finite_gram_residual c b (pulse T) f a hh.aestronglyMeasurable
    (fun i => (hf i).aestronglyMeasurable) hH hF
  have hu (i : Fin (m+1)) : AEStronglyMeasurable (u i) volume :=
    Fin.cases hh.aestronglyMeasurable (fun j => (hf j).aestronglyMeasurable) i
  have hU (i : Fin (m+1)) : Integrable (fun x => gramWeight c b x*‖u i x‖^2) :=
    Fin.cases hH hF i
  refine ⟨hi,fun i j => gramEntry_integrable c b (hu i) (hu j) (hU i) (hU j),hG,?_⟩
  intro s hs ht hz
  obtain ⟨hl,hr⟩ := abs_le.mp hs
  have h0 : 0 < s.re := by linarith
  have h1 : s.re < 1 := by linarith
  exact excludes_at_zero T c b δ hT hδ s hs ht f a
    (fun i => theta_shift_zero_integral s (y i) h0 h1 hz)
    (residual T a y) (fun _ => rfl) hm hi

end

section

open MasulloRH.GaussianApproximation Filter
open scoped Topology

namespace MasulloGram

theorem rh_of_certificates
    (hbox : ∀ (m n : ℕ) (a : Fin m → ℂ) (y : Fin m → ℝ),
      let δ : ℝ := 1/(16*((n:ℝ)+1))
      ∀ s : ℂ, |s.re-3/4| ≤ 1/4-2*δ → |s.im| ≤ (n:ℝ) → riemannZeta s = 0 →
        δ*Real.exp (-(1/2:ℝ)) ≤ energy (3/4) (1/4-δ) (residual n a y))
    (hcert : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let δ : ℝ := 1/(16*((n:ℝ)+1))
      energy (3/4) (1/4-δ) (residual n
         (fun i => ((a i).1 : ℂ) + ((a i).2 : ℂ)*Complex.I) (fun i => (y i : ℝ))) <
          δ * Real.exp (-(1/2:ℝ))) : RiemannHypothesis := by
  have hr (s : ℂ) (hs : 1/2 < s.re) (ht : s.re < 1) : riemannZeta s ≠ 0 := by
    intro h
    let w : ℝ := 1/4-|s.re-3/4|
    have hw : 0 < w := sub_pos.mpr (abs_lt.mpr ⟨by linarith,by linarith⟩)
    obtain ⟨N,hN⟩ := exists_nat_gt (max |s.im| (1/w))
    obtain ⟨n,hn,m,a,y,he⟩ := hcert N
    have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
    have hmul := (div_lt_iff₀ hw).mp ((le_max_right _ _).trans_lt hN)
    have hrec : 2/(16*((n:ℝ)+1)) ≤ w := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hn') hw.le]
    have hs' : |s.re-3/4| ≤ 1/4 - 2*(1/(16*((n:ℝ)+1))) := by dsimp [w] at hrec; simp only [div_eq_mul_inv,one_mul] at hrec ⊢; linarith
    have him := ((le_max_left _ _).trans hN.le).trans hn'
    exact he.not_ge (hbox m n _ _ s hs' him h)
  apply riemannHypothesis_iff_zeros_in_strip_on_line.mpr
  intro s hz h₀ h₁
  rcases lt_trichotomy s.re (1/2) with hl|he|hg
  · have hh (n : ℕ) : s ≠ -n := by
      intro h
      have e := congrArg Complex.re h
      simp at e
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hne : s ≠ 1 := by intro e; simp [e] at h₁
    have hz' : riemannZeta (1-s) = 0 := by rw [riemannZeta_one_sub hh hne,hz,mul_zero]
    have hl' : 1/2 < (1-s).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
    have hr' : (1-s).re < 1 := by simp only [Complex.sub_re,Complex.one_re]; linarith
    exact (hr (1-s) hl' hr' hz').elim
  · exact he
  · exact (hr s hg h₁ hz).elim

end MasulloGram

end

open MeasureTheory MasulloRH.GaussianApproximation
open scoped BigOperators ComplexConjugate

theorem solution :
    (∀ (m : ℕ) (T c b δ : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ), 0 ≤ T → 0 < δ → 0 < c-b → c+b < 1 →
    let u : Fin (m+1) → ℝ → ℂ := Fin.cons (MasulloRH.GaussianApproximation.pulse T)
      (fun i : Fin m => fun x : ℝ => MasulloRH.GaussianApproximation.theta (x-y i))
    let d : Fin (m+1) → ℂ := Fin.cons (1:ℂ) (fun i : Fin m => -a i)
    Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖residual T a y x‖^2) ∧
      (∀ i j : Fin (m+1), Integrable (fun x : ℝ => (Real.exp (2*c*x+2*b*|x|):ℂ) *
        conj (u i x) * u j x)) ∧
      energy c b (residual T a y) = (∑ i, ∑ j, conj (d i)*d j *
        ∫ x : ℝ, (Real.exp (2*c*x+2*b*|x|):ℂ)*conj (u i x)*u j x).re ∧
      (∀ s : ℂ, |s.re-c| ≤ b-δ → |s.im| ≤ T → riemannZeta s = 0 →
        δ*Real.exp (-(1/2:ℝ)) ≤ energy c b (residual T a y))) ∧
    ((∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let δ : ℝ := 1/(16*((n:ℝ)+1))
      energy (3/4) (1/4-δ) (residual n
         (fun i => ((a i).1 : ℂ) + ((a i).2 : ℂ)*Complex.I) (fun i => (y i : ℝ))) <
          δ * Real.exp (-(1/2:ℝ))) → RiemannHypothesis) := by
  constructor
  · intro m T c b δ a y hT hδ hl hr
    exact MasulloGram.rectangle T c b δ a y hT hδ hl hr
  · apply MasulloGram.rh_of_certificates
    intro m n a y δ s hs ht hz
    have hn : 0 ≤ (n:ℝ) := by positivity
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hlo : 0 < (3/4:ℝ) - (1/4-δ) := by linarith
    have hhi : (3/4:ℝ) + (1/4-δ) < 1 := by linarith
    exact (MasulloGram.rectangle n (3/4) (1/4-δ) δ a y hn hδ hlo hhi).2.2.2 s (by linarith) ht hz
