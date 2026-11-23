-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_gaussian_fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:44:53.925807+00:00
-- url     : https://prove2.me/submissions/082d1e04-82d4-4089-92b1-4efa63374039

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real


open MeasureTheory Real GrothendieckLB.Supplement.CQPrice
namespace CQGaussianMoment

noncomputable def raw (b : ℝ) (k : ℕ) := ∫ x : ℝ, |x|^k * exp (-b*x^2)

theorem raw_integrable (b : ℝ) (hb : 0<b) (k : ℕ) :
    Integrable (fun x : ℝ => |x|^k*exp (-b*x^2)) := by
  have hk : -1 < (k:ℝ) := by linarith [(show 0≤(k:ℝ) by positivity)]
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb hk).norm
  simpa only [Real.rpow_natCast, Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (exp_pos _)] using h


end CQGaussianMoment


open MeasureTheory Real GrothendieckLB.Supplement.CQPrice CQGaussianMoment Filter
open scoped Topology
namespace CQFourierDerivative
noncomputable def phase (q u v : ℂ) (w : ℝ×ℝ) :=
  -(((w.1:ℂ)^2 + (w.2:ℂ)^2 + 2*q*w.1*w.2)/2) + Complex.I*(u*w.1+v*w.2)
noncomputable def osc (q u v : ℂ) (m n : ℕ) (w : ℝ×ℝ) :=
  (Complex.I*(w.1:ℂ))^m * (Complex.I*(w.2:ℂ))^n*Complex.exp (phase q u v w)

noncomputable def env (R : ℝ) (m n : ℕ) (w : ℝ×ℝ) :=
  (|w.1|^m*exp (-((1-R)/2)*w.1^2))*(|w.2|^n*exp (-((1-R)/2)*w.2^2))

theorem env_int {R : ℝ} (hR : R<1) (m n : ℕ) : Integrable (env R m n) := by
  have hb : 0<(1-R)/2 := by linarith
  exact (raw_integrable _ hb m).mul_prod (raw_integrable _ hb n)

theorem kernel_le {R t : ℝ} (ht : |t|≤R) (x y : ℝ) :
    -(x^2+y^2+2*t*x*y)/2 ≤ -((1-R)/2)*x^2 + -((1-R)/2)*y^2 := by
  have hn : 0≤R := (abs_nonneg _).trans ht
  obtain ⟨hl,hh⟩ := abs_le.mp ht
  by_cases h : 0≤x*y
  · nlinarith only [mul_le_mul_of_nonneg_right hl h,mul_nonneg hn (sq_nonneg (x-y))]
  · nlinarith only [mul_le_mul_of_nonpos_right hh (le_of_not_ge h),mul_nonneg hn (sq_nonneg (x+y))]

theorem norm_osc (q : ℂ) (u v : ℝ) (m n : ℕ) (w : ℝ×ℝ) :
    ‖osc q u v m n w‖ = |w.1|^m*|w.2|^n*exp (-(w.1^2+w.2^2+2*q.re*w.1*w.2)/2) := by
  simp only [osc,norm_mul,norm_pow,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
  congr 2
  unfold phase
  rw [div_eq_mul_inv]
  simp [Complex.add_re,Complex.neg_re,Complex.mul_re,Complex.mul_im,pow_two]
  <;> ring

theorem osc_le (q : ℂ) (u v : ℝ) (m n : ℕ) (w : ℝ×ℝ) (R : ℝ) (h : |q.re|≤R) :
    ‖osc q u v m n w‖ ≤ env R m n w := by
  rw [norm_osc]
  calc
    _ ≤ |w.1|^m*|w.2|^n*(exp (-((1-R)/2)*w.1^2)*exp (-((1-R)/2)*w.2^2)) := by
      rw [← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (kernel_le h _ _)) (by positivity)
    _ = _ := by unfold env;ring

theorem cont (q u v : ℂ) (m n : ℕ) : Continuous (osc q u v m n) := by unfold osc phase;fun_prop
theorem osc_int (q : ℂ) (hq : |q.re|<1) (u v : ℝ) (m n : ℕ) :
    Integrable (osc q u v m n) :=
  (env_int hq m n).mono' (cont _ _ _ _ _).aestronglyMeasurable (Eventually.of_forall fun w => osc_le _ _ _ _ _ w _ le_rfl)


end CQFourierDerivative


open MeasureTheory Real GrothendieckLB.Supplement.CQPrice CQFourierDerivative
namespace CQGaussianInversion
private theorem scale_cpow (r : ℝ) (hr : 0<r) {x : ℂ} (hx : x≠0) (w : ℂ) :
    ((r:ℂ)*x)^w=(r:ℂ)^w*x^w := by
  have hr' : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr' hx),Complex.cpow_def_of_ne_zero hr',
    Complex.cpow_def_of_ne_zero hx,Complex.log_ofReal_mul hr hx,Complex.ofReal_log hr.le,add_mul,Complex.exp_add]

private theorem prefactor (q : ℂ) (hq : ‖q‖<1) :
    (2*Real.pi:ℂ)^(1/2:ℂ)*((2*Real.pi:ℂ)/(1-q^2))^(1/2:ℂ)=
      (2*Real.pi:ℂ)*(1-q^2)^(-(1/2:ℂ)) := by
  have hs : 1-q^2∈Complex.slitPlane := by
    rw [sub_eq_add_neg]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_neg,norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by decide)
  have hn := Complex.slitPlane_ne_zero hs
  have hp : (2*Real.pi:ℂ)=((2*Real.pi:ℝ):ℂ) := by push_cast;rfl
  rw [div_eq_mul_inv (2*(Real.pi:ℂ)) (1-q^2),hp,scale_cpow _ (by positivity) (inv_ne_zero hn),
    Complex.inv_cpow _ _ (Complex.slitPlane_arg_ne_pi hs),← mul_assoc,← sq,
    ← Complex.cpow_nat_mul,Complex.cpow_neg]
  norm_num
  
private noncomputable def b (q : ℂ) := -(1-q^2)/2
private noncomputable def c (q : ℂ) (u v : ℝ) := Complex.I*((u:ℂ)-q*v)

theorem solution_aux (q : ℂ) (hq : ‖q‖<1) (u v : ℝ) :
    fourierMoment q u v 0 0=(2*Real.pi:ℂ)*density q u v := by
  have ht := (Complex.abs_re_le_norm q).trans_lt hq
  have hr : 0 < (1-q^2).re := by
    have h₁ := (abs_lt.mp ht).1
    have h₂ := (abs_lt.mp ht).2
    simp [pow_two,Complex.mul_re]
    nlinarith [sq_nonneg q.im,mul_pos (show 0<1-q.re by linarith) (show 0<1+q.re by linarith)]
  have hn : 1-q^2≠0 := fun h => by simpa [h] using hr
  have hplus : 1+q≠0 := by intro h;apply hn;linear_combination (1-q)*h
  have hminus : 1-q≠0 := by intro h;apply hn;linear_combination (1+q)*h
  have hb : (b q).re < 0 := by
    unfold b
    rw [div_eq_mul_inv]
    simp [Complex.mul_re] at *
    linarith
  have hI : Integrable (fun w : ℝ×ℝ => Complex.exp (phase q u v w)) :=
    by
      have hi := osc_int q ht u v 0 0
      have he : osc q u v 0 0=(fun w => Complex.exp (phase q u v w)) := by funext w;simp [osc]
      rwa [he] at hi
  have inner (x : ℝ) : (∫ y : ℝ, Complex.exp (phase q u v (x,y))) =
    (2*Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (b q*(x:ℂ)^2+c q u v*x-(v:ℂ)^2/2) := by
    let c₀ := -q*(x:ℂ)+Complex.I*v
    let d₀ := -(x:ℂ)^2/2+Complex.I*u*x
    have hphase (y : ℝ) : phase q u v (x,y)=(-1/2:ℂ)*(y:ℂ)^2+c₀*y+d₀ := by unfold phase c₀ d₀;ring
    simp_rw [hphase]
    rw [integral_cexp_quadratic (b:=(-1/2:ℂ)) (by norm_num) c₀ d₀]
    congr 2
    · ring
    · dsimp [c₀,d₀,b,c]
      ring_nf
      simp only [Complex.I_sq]
      ring
  unfold fourierMoment
  push_cast
  change (1/(2*Real.pi):ℂ)*(∫ w : ℝ×ℝ, (Complex.I*(w.1:ℂ))^0*(Complex.I*(w.2:ℂ))^0*
    Complex.exp (phase q u v w) ∂volume.prod volume)=_
  simp only [pow_zero,one_mul]
  rw [integral_prod _ hI]
  simp_rw [inner]
  rw [integral_const_mul]
  have outer (x : ℝ) : b q*(x:ℂ)^2+c q u v*x-(v:ℂ)^2/2 =
      b q*(x:ℂ)^2+c q u v*x+(-(v:ℂ)^2/2) := by ring
  simp_rw [outer]
  rw [integral_cexp_quadratic hb]
  have hbv : (Real.pi:ℂ)/(-b q)=(2*Real.pi:ℂ)/(1-q^2) := by unfold b;field_simp [hn] <;> ring
  have hex : -(v:ℂ)^2/2-c q u v^2/(4*b q) =
    -(((((u+v)^2/4:ℝ):ℂ) * (1+q)⁻¹) + ((((u-v)^2/4:ℝ):ℂ)*(1-q)⁻¹)) := by
    unfold b c
    push_cast
    rw [mul_pow,Complex.I_sq]
    field_simp [hn,hplus,hminus]
    <;> ring
  rw [hbv,hex,← mul_assoc ((2*Real.pi:ℂ)^(1/2:ℂ)),prefactor q hq,density]
  push_cast
  field_simp [Real.pi_ne_zero]
  <;> ring
end CQGaussianInversion

open CQGaussianInversion in
theorem solution (q : ℂ) (hq : ‖q‖<1) (u v : ℝ) :
    fourierMoment q u v 0 0=(2*Real.pi:ℂ)*density q u v := solution_aux q hq u v