-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_gaussian_fourier_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:28:18.743954+00:00
-- url     : https://prove2.me/submissions/396c9ba5-3669-4899-8203-f3c45f43da61

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral


open MeasureTheory Real GrothendieckLB.Supplement.CQPrice
namespace CQGaussianMoment

noncomputable def raw (b : ℝ) (k : ℕ) := ∫ x : ℝ, |x|^k * exp (-b*x^2)

theorem raw_integrable (b : ℝ) (hb : 0<b) (k : ℕ) :
    Integrable (fun x : ℝ => |x|^k*exp (-b*x^2)) := by
  have hk : -1 < (k:ℝ) := by linarith [(show 0≤(k:ℝ) by positivity)]
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb hk).norm
  simpa only [Real.rpow_natCast, Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (exp_pos _)] using h

theorem raw_gamma (b : ℝ) (hb : 0<b) (k : ℕ) :
    raw b k=b^(-((k:ℝ)+1)/2)*Gamma (((k:ℝ)+1)/2) := by
  have hk : -1 < (k:ℝ) := by linarith [(show 0≤(k:ℝ) by positivity)]
  have h := integral_rpow_mul_exp_neg_mul_rpow (p:=(2:ℝ)) two_pos hk hb
  simp only [Real.rpow_natCast,Real.rpow_two] at h
  have hspec := integral_comp_abs (f := fun x : ℝ => x^k*exp (-b*x^2))
  simp only [sq_abs] at hspec
  rw [raw,hspec,h]
  ring

theorem raw_step (b : ℝ) (hb : 0<b) (k : ℕ) :
    raw b (k+2)=((k:ℝ)+1)/(2*b)*raw b k := by
  have h0 : ((k:ℝ)+1)/2≠0 := by positivity
  rw [raw_gamma b hb (k+2),raw_gamma b hb k]
  push_cast
  rw [show ((k:ℝ)+2+1)/2 = ((k:ℝ)+1)/2+1 by ring,
    show -((k:ℝ)+2+1)/2 = -((k:ℝ)+1)/2+(-1) by ring,
    Real.rpow_add hb, Real.rpow_neg_one, Real.Gamma_add_one h0]
  ring

theorem raw_zero (b : ℝ) : raw b 0=Real.sqrt (Real.pi/b) := by simpa only [raw,pow_zero,one_mul] using integral_gaussian b
theorem raw_first_quarter : raw (1/4) 1=4 := by
  rw [raw_gamma (1/4) (by norm_num)]
  norm_num [Real.Gamma_one]

theorem df_step (m : ℕ) : momentDF (m+1)=(2*m+1)*momentDF m := by
  unfold momentDF
  rw [show 2*(m+1)-1 = 2*m+1 by omega,Nat.doubleFactorial_add_one]

theorem even (b : ℝ) (hb : 0<b) (m : ℕ) :
    raw b (2*m)=Real.sqrt (Real.pi/b)*(1/(2*b))^m*(momentDF m:ℝ) := by
  induction m with
  | zero => simp [momentDF,Nat.doubleFactorial,raw_zero]
  | succ m ih =>
    rw [show 2*(m+1)=2*m+2 by omega,raw_step b hb,ih,pow_succ,df_step]
    push_cast
    ring

noncomputable def normal (k : ℕ) := ∫ x : ℝ, normalTwo x * |x|^k
theorem normal_eq (k : ℕ) : normal k = (1/(2*Real.sqrt Real.pi))*raw (1/4) k := by
  dsimp [normal,raw,normalTwo]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [show -(1/4:ℝ)*x^2= -(x^2)/4 by ring]
  ring

theorem normal_integrable (k : ℕ) : Integrable (fun x : ℝ => normalTwo x * |x|^k) := by
  convert (raw_integrable (1/4) (by norm_num) k).const_mul (1/(2*Real.sqrt Real.pi)) using 1
  funext x
  dsimp [normalTwo]
  rw [show -(1/4:ℝ)*x^2= -(x^2)/4 by ring]
  ring

theorem normal_step (k : ℕ) : normal (k+2)=2*((k:ℝ)+1)*normal k := by
  rw [normal_eq,raw_step _ (by norm_num),normal_eq]
  ring

theorem normal_zero : normal 0=1 := by
  rw [normal_eq,raw_zero,show Real.pi/(1/4)=4*Real.pi by ring, Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  rw [show Real.sqrt (4:ℝ)=2 by rw [show (4:ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num)]]
  field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']
theorem normal_one : normal 1=2/Real.sqrt Real.pi := by rw [normal_eq,raw_first_quarter]; ring
end CQGaussianMoment


open MeasureTheory Real GrothendieckLB.Supplement.CQPrice CQGaussianMoment
namespace CQGaussianFourier

noncomputable def kernel (t x y : ℝ) := Real.exp (-(x^2+y^2+2*t*x*y)/2)
noncomputable def marginal (t : ℝ) (k : ℕ) (w : ℝ×ℝ) := |w.1|^(2*k)*kernel t w.1 w.2
noncomputable def sig (t : ℝ) := (Real.sqrt (1-t^2))⁻¹
noncomputable def dev (t : ℝ) (k : ℕ) := sig t^k*Real.sqrt (momentDF k:ℝ)

private theorem gap (t : ℝ) (ht : |t|<1) : 0<1-t^2 := by
  obtain ⟨h₁,h₂⟩ := abs_lt.mp ht
  nlinarith [mul_pos (show 0<1-t by linarith) (show 0<1+t by linarith)]
private theorem sig_pos (t : ℝ) (ht : |t|<1) : 0<sig t := inv_pos.mpr (Real.sqrt_pos.mpr (gap t ht))
private theorem df_pos (k : ℕ) : 0<(momentDF k:ℝ) := by
  exact_mod_cast Nat.doubleFactorial_pos (2*k-1)
private theorem dev_pos (t : ℝ) (ht : |t|<1) (k : ℕ) : 0<dev t k :=
  mul_pos (pow_pos (sig_pos t ht) _) (Real.sqrt_pos.mpr (df_pos k))

private theorem factor (t : ℝ) (k : ℕ) (x y : ℝ) :
    marginal t k (x,y) =
      (|x|^(2*k)*Real.exp (-((1-t^2)/2)*x^2)) * Real.exp (-(1/2:ℝ)*(y+t*x)^2) := by
  dsimp [marginal,kernel]
  rw [mul_assoc (|x|^(2*k)) (Real.exp _) (Real.exp _),← Real.exp_add]
  congr 2 <;> ring

private theorem inner (t : ℝ) (k : ℕ) (x : ℝ) :
    (∫ y : ℝ, marginal t k (x,y)) =
      (|x|^(2*k)*Real.exp (-((1-t^2)/2)*x^2))*Real.sqrt (2*Real.pi) := by
  simp_rw [factor]
  rw [integral_const_mul]
  congr 1
  calc
    _ = ∫ y : ℝ, Real.exp (-(1/2:ℝ)*y^2) := integral_add_right_eq_self (fun y : ℝ => Real.exp (-(1/2:ℝ)*y^2)) (t*x)
    _ = _ := by rw [integral_gaussian];congr 1;ring

private theorem marginal_int (t : ℝ) (ht : |t|<1) (k : ℕ) : Integrable (marginal t k) := by
  have hb : 0<(1-t^2)/2 := by linarith [gap t ht]
  have hcont : Continuous (marginal t k) := by unfold marginal kernel;fun_prop
  apply (integrable_prod_iff (μ:=volume) (ν:=volume) hcont.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (fun x => ?_),?_⟩
  · simp_rw [factor]
    exact ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/2)).comp_add_right (t*x)).const_mul _
  · have hn (x y : ℝ) : ‖marginal t k (x,y)‖=marginal t k (x,y) := by
      rw [Real.norm_eq_abs,abs_of_nonneg];unfold marginal kernel;positivity
    simp_rw [hn,inner]
    exact (raw_integrable _ hb _).mul_const _

private theorem marginal_value (t : ℝ) (ht : |t|<1) (k : ℕ) :
    (∫ w : ℝ×ℝ, marginal t k w) = 2*Real.pi*sig t*(dev t k)^2 := by
  have ha := gap t ht
  have hb : 0<(1-t^2)/2 := by linarith
  have hs := Real.sqrt_pos.mpr ha
  have hp := Real.sqrt_pos.mpr (by positivity : 0<2*Real.pi)
  change (∫ w : ℝ×ℝ, marginal t k w ∂volume.prod volume)=_
  rw [integral_prod _ (marginal_int t ht k)]
  simp_rw [inner]
  rw [integral_mul_const]
  change raw ((1-t^2)/2) (2*k)*_ = _
  rw [even _ hb]
  have sqeq : Real.sqrt (Real.pi/((1-t^2)/2))= Real.sqrt (2*Real.pi)/Real.sqrt (1-t^2) := by
    rw [← Real.sqrt_div (by positivity : (0:ℝ)≤2*Real.pi)]
    congr 1
    field_simp [ha.ne'] <;> ring
  have sigsq : 1/(2*((1-t^2)/2))=(sig t)^2 := by
    unfold sig
    rw [inv_pow,Real.sq_sqrt ha.le]
    ring
  rw [sqeq,sigsq,dev,mul_pow,Real.sq_sqrt (df_pos k).le]
  have hpow : (sig t ^ 2)^k = (sig t^k)^2 := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  rw [hpow]
  calc
    _ = (Real.sqrt (2*Real.pi))^2*sig t*((sig t)^k)^2*(momentDF k:ℝ) := by unfold sig;ring
    _ = _ := by rw [Real.sq_sqrt (by positivity : (0:ℝ)≤2*Real.pi)];ring

private theorem envelope_formula (q : ℂ) (u v : ℝ) (m n : ℕ) (w : ℝ×ℝ) :
    ‖(Complex.I*(w.1:ℂ))^m*(Complex.I*(w.2:ℂ))^n *
      Complex.exp (-(((w.1:ℂ)^2 + (w.2:ℂ)^2 + 2*q*w.1*w.2)/2)+
        Complex.I*((u:ℂ)*w.1+(v:ℂ)*w.2))‖ =
    |w.1|^m*|w.2|^n*kernel q.re w.1 w.2 := by
  simp only [norm_mul,norm_pow,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
  congr 2
  rw [div_eq_mul_inv]
  simp [Complex.add_re,Complex.neg_re,Complex.mul_re,Complex.mul_im,pow_two]
  <;> ring

private theorem young (a b X Y : ℝ) (ha : 0<a) (hb : 0<b) :
    X*Y ≤ (b^2*X^2+a^2*Y^2)/(2*a*b) := by
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [sq_nonneg (b*X-a*Y)]


private noncomputable def osc (q : ℂ) (u v : ℝ) (m n : ℕ) (w : ℝ×ℝ) :=
  (Complex.I*(w.1:ℂ))^m*(Complex.I*(w.2:ℂ))^n *
    Complex.exp (-(((w.1:ℂ)^2+(w.2:ℂ)^2+2*q*w.1*w.2)/2)+Complex.I*((u:ℂ)*w.1+(v:ℂ)*w.2))

private theorem kernel_swap (t x y : ℝ) : kernel t y x=kernel t x y := by
  unfold kernel
  congr 1
  ring

theorem bound (q : ℂ) (ht : |q.re|<1) (u v : ℝ) (m n : ℕ) :
    ‖fourierMoment q u v m n‖ ≤ sig q.re^(m+n+1)*Real.sqrt ((momentDF m:ℝ)*(momentDF n:ℝ)) := by
  let t := q.re
  let A := dev t m
  let B := dev t n
  have hA : 0<A := dev_pos _ ht _
  have hB : 0<B := dev_pos _ ht _
  let f := marginal t m
  let g := fun w : ℝ×ℝ => marginal t n w.swap
  let U := fun w : ℝ×ℝ => (B^2*f w+A^2*g w)/(2*A*B)
  have hf : Integrable f := marginal_int _ ht _
  have hg : Integrable g := (marginal_int _ ht n).swap
  have hU : Integrable U := ((hf.const_mul (B^2)).add (hg.const_mul (A^2))).div_const _
  have hmajor (w : ℝ×ℝ) : ‖osc q u v m n w‖ ≤ U w := by
    rw [osc,envelope_formula]
    calc
      _ ≤ ((B^2*(|w.1|^m)^2 + A^2*(|w.2|^n)^2)/(2*A*B))*kernel t w.1 w.2 :=
        mul_le_mul_of_nonneg_right (young A B _ _ hA hB) (Real.exp_pos _).le
      _ = _ := by
        dsimp only [U,f,g,marginal,Prod.swap]
        rw [kernel_swap t w.1 w.2,← pow_mul,← pow_mul,Nat.mul_comm m 2,Nat.mul_comm n 2]
        ring
  have hgval : (∫ w : ℝ×ℝ, g w)=2*Real.pi*sig t*B^2 := by
    calc
      _ = ∫ w : ℝ×ℝ, marginal t n w :=
        integral_prod_swap (μ:=volume) (ν:=volume) (marginal t n)
      _ = _ := marginal_value _ ht _
  have hfval : (∫ w : ℝ×ℝ, f w)=2*Real.pi*sig t*A^2 := marginal_value _ ht _
  have evalU : (∫ w : ℝ×ℝ, U w)=2*Real.pi*sig t*A*B := by
    dsimp only [U]
    rw [integral_div,integral_add (hf.const_mul _) (hg.const_mul _),integral_const_mul,integral_const_mul,hfval,hgval]
    field_simp [hA.ne',hB.ne']
    <;> ring
  change ‖((1/(2*Real.pi):ℝ):ℂ)*(∫ w : ℝ×ℝ, osc q u v m n w)‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤1/(2*Real.pi))]
  calc
    _ ≤ 1/(2*Real.pi)*(∫ w : ℝ×ℝ, U w) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hU (Filter.Eventually.of_forall hmajor)) (by positivity)
    _ = _ := by
      rw [evalU,pow_succ,pow_add,Real.sqrt_mul (df_pos m).le]
      dsimp only [A,B,dev,t]
      field_simp [Real.pi_pos.ne']
      <;> ring

end CQGaussianFourier

open CQGaussianFourier in
theorem solution (q : ℂ) (hq : |q.re|<1) (u v : ℝ) (m n : ℕ) :
    ‖fourierMoment q u v m n‖ ≤ ((Real.sqrt (1-q.re^2))⁻¹)^(m+n+1) *
      Real.sqrt ((momentDF m:ℝ)*(momentDF n:ℝ)) := bound q hq u v m n
