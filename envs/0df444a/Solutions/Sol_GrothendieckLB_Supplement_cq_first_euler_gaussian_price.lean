-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_first_euler_gaussian_price
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:41:54.319686+00:00
-- url     : https://prove2.me/submissions/ada117ad-5687-46d7-9f0f-227e7f6038a0

import Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_hermite_expansion
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel
import Theorems.Thm_GrothendieckLB_Supplement_cqA_sextic_reduction
import Theorems.Thm_GrothendieckLB_Supplement_gaussian_hermite_integration_by_parts
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_9
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib

open Filter MeasureTheory ProbabilityTheory Real Polynomial GrothendieckLB.Supplement CQBoundary
open scoped Topology
set_option maxHeartbeats 1400000
noncomputable section
namespace GaussianDensitySeries

open Polynomial Finset Real MeasureTheory ProbabilityTheory
open PrivateAgnosticHalfspace.Gaussian

private theorem herm_compat (n : ℕ) (x : ℝ) : AMPLowDeg.RankOne.hermNorm n x = QuadSDE.hermiteN n x := by
  unfold AMPLowDeg.RankOne.hermNorm QuadSDE.hermiteN
  rw [eval_map]
  rfl

private theorem scalar_mehler (r x y : ℝ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => r^n * QuadSDE.hermiteN n x * QuadSDE.hermiteN n y)
      ((1-r^2)^(-(1:ℝ)/2) * exp ((2*r*x*y-r^2*(x^2+y^2))/(2*(1-r^2)))) := by
  let X : Vec 1 := WithLp.toLp 2 (fun _ => x)
  let Y : Vec 1 := WithLp.toLp 2 (fun _ => y)
  have hm := lemma_B_9 1 X Y r (abs_lt.mp hr)
  let e := (Equiv.funUnique (Fin 1) ℕ).symm
  have h := e.hasSum_iff.mpr hm
  have e0 (n : ℕ) : e n 0 = n := rfl
  have hnX : ‖X‖^2=x^2 := by simp [X,EuclideanSpace.norm_sq_eq,Fin.sum_univ_one,Real.norm_eq_abs]
  have hnY : ‖Y‖^2=y^2 := by simp [Y,EuclideanSpace.norm_sq_eq,Fin.sum_univ_one,Real.norm_eq_abs]
  have hxy : inner ℝ X Y = x*y := by simp [PiLp.inner_apply,X,Y,Fin.sum_univ_one,Real.inner_apply,mul_comm]
  rw [hxy,hnX,hnY] at h
  simpa only [Function.comp_def,PrivateAgnosticHalfspace.Gaussian.hermite,PrivateAgnosticHalfspace.Gaussian.degree,Fin.sum_univ_one,Fin.prod_univ_one,e0,
    X,Y,WithLp.ofLp_toLp,herm_compat,Nat.cast_one,mul_assoc] using h


end GaussianDensitySeries
namespace PriceCoefficients
open GaussianDensitySeries

private abbrev γ : Measure ℝ := gaussianReal 0 1
private def U (x : ℝ) := slope*(x^3-3*x)
private def U1 (x : ℝ) := slope*(3*x^2-3)
private def A (a b : ℕ) := cqA 0.136419125 0.34101124 0.05276111 a b
private def h (n : ℕ) := QuadSDE.hermiteN n
private def mon (n : ℕ) (t : ℝ) : ℝ := aeval t (hermite n)
private def w (t : ℝ) := exp (-(t^2)/2)
private def Q (n : ℕ) (u : ℝ) := w u * h n (-u)
private def d := sqrt (2*Real.pi)
private def sf (n : ℕ) := Real.sqrt (n.factorial:ℝ)
private def c := Real.pi/d
private def B (a b : ℕ) := ∫ x : ℝ, Q a (U x)*h b x ∂γ
private def V (a b : ℕ) := ∫ x : ℝ, U1 x*Q a (U x)*h b x ∂γ
private theorem dpos : 0 < d := by unfold d; positivity
private theorem sfpos (a : ℕ) : 0 < sf a := by unfold sf; positivity
private theorem sf_succ (a : ℕ) : sf (a+1) = sqrt ((a:ℝ)+1)*sf a := by
  simp only [sf,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,sqrt_mul (by positivity : 0 ≤ (a:ℝ)+1)]
private theorem wneg (x : ℝ) : w (-x) = w x := by simp [w]
private theorem lawPDF (x : ℝ) : gaussianPDFReal 0 1 x = d⁻¹*w x := by simp [gaussianPDFReal,w,d]
private theorem ew (x : ℝ) : w (U x)*w x = exp (-(x^2+(slope*(x^3-3*x))^2)/2) := by
  rw [w,w,← Real.exp_add]
  congr 1; dsimp [U]; ring
private theorem sb (a b : ℕ) : B a b = c*sqrt ((a:ℝ)+1)*A (a+1) b := by
  have h0 := (cqA_sextic_reduction 0.136419125 0.34101124 0.05276111).1 a b
  change Real.pi*sf (a+1)*sf b*A (a+1) b = ∫ x : ℝ, mon a (-(slope)*(x^3-3*x))*mon b x*exp (-(x^2+(slope*(x^3-3*x))^2)/2) at h0
  let P (x : ℝ) := mon a (-slope*(x^3-3*x))*mon b x*exp (-(x^2+(slope*(x^3-3*x))^2)/2)
  have e (x : ℝ) : gaussianPDFReal 0 1 x • (Q a (U x)*h b x) = (d*sf a*sf b)⁻¹*P x := by
    rw [lawPDF]
    simp only [smul_eq_mul,Q,h,QuadSDE.hermiteN,P,← ew,mon,sf]
    rw [show -slope*(x^3-3*x) = -(U x) by dsimp [U]; ring]
    ring
  unfold B
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  simp_rw [e,integral_const_mul]
  change (d*sf a*sf b)⁻¹*(∫ x : ℝ, P x) = _
  change _ = ∫ x : ℝ, P x at h0
  rw [← h0,sf_succ]
  dsimp [c]
  field_simp [(sfpos a).ne',(sfpos b).ne',dpos.ne']
private theorem sv0 (b : ℕ) : V 0 b = c*sqrt ((b:ℝ)+1)*A 0 (b+1) := by
  have h0 := (cqA_sextic_reduction 0.136419125 0.34101124 0.05276111).2 b
  let P (x : ℝ) := (x^2-1)*mon b x*exp (-(x^2+(slope*(x^3-3*x))^2)/2)
  change Real.pi*sf (b+1)*A 0 (b+1) = 3*slope*∫ x : ℝ, P x at h0
  have hzero (v : ℝ) : h 0 v=1 := by simp [h,QuadSDE.hermiteN,hermite_zero]
  have e (x : ℝ) : gaussianPDFReal 0 1 x • (U1 x*Q 0 (U x)*h b x) = (d*sf b)⁻¹*(3*slope*P x) := by
    rw [lawPDF]
    simp only [Q,hzero]
    simp only [smul_eq_mul,h,QuadSDE.hermiteN,P,← ew,mon,sf,U1]
    ring
  unfold V
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  simp_rw [e]
  rw [integral_const_mul,integral_const_mul,← h0,sf_succ]
  dsimp [c]
  field_simp [(sfpos b).ne',dpos.ne']
private theorem monD (a : ℕ) (t : ℝ) : HasDerivAt (fun u : ℝ => mon a u*w u)
    (-(mon (a+1) t*w t)) t := by
  have hw : HasDerivAt w ((-t)*w t) t := by
    apply ((((hasDerivAt_pow 2 t).neg).div_const 2).exp).congr_deriv
    dsimp [w]; ring
  apply (((hermite a).hasDerivAt_aeval t).mul hw).congr_deriv
  simp only [mon,hermite_succ,map_sub,map_mul,aeval_X]; ring
private theorem dU (x : ℝ) : HasDerivAt U (U1 x) x := by
  apply (((hasDerivAt_pow 3 x).sub ((hasDerivAt_id x).const_mul 3)).const_mul slope).congr_deriv
  simp [U1]
private theorem qD (a : ℕ) (x : ℝ) : HasDerivAt (fun t : ℝ => Q a (U t))
    (sqrt ((a:ℝ)+1)*U1 x*Q (a+1) (U x)) x := by
  have hd := (((monD a (-(U x))).comp x (dU x).neg).div_const (sf a))
  have ef (t : ℝ) : Q a (U t) = (mon a (-(U t))*w (-(U t)))/sf a := by
    rw [wneg]; change w (U t)*(mon a (-(U t))/sf a) = _; ring
  apply (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall ef)).congr_deriv
  change -(mon (a+1) (-(U x))*w (-(U x)))*(-U1 x)/sf a =
    sqrt ((a:ℝ)+1)*U1 x*(w (U x)*(mon (a+1) (-(U x))/sf (a+1)))
  rw [wneg,sf_succ]
  field_simp [(sfpos a).ne',show Real.sqrt ((a:ℝ)+1) ≠ 0 by positivity]
private def R (r u v : ℝ) := (1-r^2)^(-(1:ℝ)/2)*exp (-(u^2-2*r*u*v+v^2)/(2*(1-r^2)))
private theorem denpos (r : ℝ) (hr : |r| < 1) : 0 < 1-r^2 := by
  have he := abs_lt.mp hr
  nlinarith only [mul_pos (show 0 < 1+r by linarith only [he.1]) (sub_pos.mpr he.2)]
private theorem qSeries (r u v : ℝ) (hr : |r| < 1) :
    HasSum (fun a : ℕ => r^a*Q a u*Q a v) (R r u v) := by
  have hh := (scalar_mehler r (-u) (-v) hr).mul_right (w u*w v)
  have hd := (denpos r hr).ne'
  have he : (2*r*(-u)*(-v)-r^2*((-u)^2+(-v)^2))/(2*(1-r^2)) +
      (-(u^2)/2) + (-(v^2)/2) = -(u^2-2*r*u*v+v^2)/(2*(1-r^2)) := by
    field_simp [hd]; ring
  have he' : (1-r^2)^(-(1:ℝ)/2)*exp ((2*r*(-u)*(-v)-r^2*((-u)^2+(-v)^2))/(2*(1-r^2)))*(w u*w v)=R r u v := by
    unfold w R
    rw [← he,Real.exp_add,Real.exp_add]
    ring
  rw [he'] at hh
  exact hh.congr_fun (fun n => by simp only [Q,h]; ring)
private theorem boundQ (a : ℕ) (u : ℝ) : |Q a u| ≤ 2*2^a := by
  have h : (1/2:ℝ)^a*Q a u*Q a u ≤ R (1/2) u u :=
    le_hasSum (qSeries (1/2) u u (by norm_num)) a (fun n _ => by
      have := mul_nonneg (show 0 ≤ (1/2:ℝ)^n by positivity) (sq_nonneg (Q n u))
      nlinarith only [this])
  have e : -(u^2-2*(1/2)*u*u+u^2)/(2*(1-(1/2)^2))= -((2/3)*u^2) := by ring
  have hC : ((1-(1/2)^2:ℝ)^(-(1:ℝ)/2)) ≤ 2 := by
    rw [show -(1:ℝ)/2=-(1/2) by ring,rpow_neg (by norm_num),← Real.sqrt_eq_rpow]
    apply (inv_le_comm₀ (by positivity) (by norm_num : (0:ℝ)<2)).2
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hx : R (1/2) u u ≤ 2 := by
    rw [R,e]
    exact (mul_le_of_le_one_right (rpow_nonneg (by norm_num) _) (exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))).trans hC
  have h' := mul_le_mul_of_nonneg_left (h.trans hx) (show (0:ℝ) ≤ 2^a by positivity)
  rw [one_div,inv_pow] at h'
  have hy : |Q a u|^2 ≤ 2*2^a := by
    rw [sq_abs]
    calc _ = 2^a*((2^a:ℝ)⁻¹*Q a u*Q a u) := by field_simp
         _ ≤ _ := by simpa [mul_comm 2 (2^a:ℝ)] using h'
  have hn : (1:ℝ) ≤ 2^a := one_le_pow₀ (by norm_num)
  nlinarith only [hy,sq_nonneg (|Q a u|-1),hn]
private theorem q_cont (a : ℕ) : Continuous (Q a) := by unfold Q w h QuadSDE.hermiteN; fun_prop
private theorem q_intParts (a b : ℕ) :
    sqrt ((a:ℝ)+1)*V (a+1) b = sqrt ((b:ℝ)+1)*B a (b+1) := by
  let f (x : ℝ) := Q a (U x)
  let g (x : ℝ) := sqrt ((a:ℝ)+1)*U1 x*Q (a+1) (U x)
  have hg : Continuous g := by
    unfold g U1 U; exact (continuous_const.mul (by fun_prop)).mul ((q_cont _).comp (by fun_prop))
  have hb (x : ℝ) : ‖(f x : ℂ)‖+‖(g x : ℂ)‖ ≤
      (2*2^a + sqrt ((a:ℝ)+1)* |slope| *3*(2*2^(a+1)))*(1+x^2)^1 := by
    simp only [Complex.norm_real,Real.norm_eq_abs,f,g,U1,abs_mul,abs_of_nonneg (sqrt_nonneg _),pow_one]
    have hx : |3*x^2-3| ≤ 3*(1+x^2) := by rw [abs_le]; constructor <;> nlinarith only [sq_nonneg x]
    have hq := mul_le_mul_of_nonneg_left (mul_le_mul hx (boundQ (a+1) (U x)) (abs_nonneg _) (by positivity))
      (mul_nonneg (sqrt_nonneg ((a:ℝ)+1)) (abs_nonneg slope))
    have h0 := boundQ a (U x)
    have hw := mul_nonneg (show (0:ℝ) ≤ 2*2^a by positivity) (sq_nonneg x)
    nlinarith only [hq,h0,hw]
  have hi := gaussian_hermite_integration_by_parts (fun t => Complex.ofReal (f t)) (fun t => Complex.ofReal (g t))
    (Complex.continuous_ofReal.comp hg) (fun x => (qD a x).ofReal_comp) _ _ hb b
  have hI (q : ℝ → ℝ) (m : ℕ) : (∫ t, Complex.ofReal (q t)*Complex.ofReal (QuadSDE.hermiteN m t) ∂γ) =
      Complex.ofReal (∫ t, q t*h m t ∂γ) := by simp only [h,← Complex.ofReal_mul,integral_complex_ofReal]
  change (∫ t, Complex.ofReal (g t)*Complex.ofReal (QuadSDE.hermiteN b t) ∂γ) = _ at hi
  rw [hI,hI,← Complex.ofReal_mul] at hi
  have hR := Complex.ofReal_inj.mp hi
  have e (t : ℝ) : g t*h b t = sqrt ((a:ℝ)+1)*(U1 t*Q (a+1) (U t)*h b t) := by unfold g; ring
  simp only [e,integral_const_mul] at hR
  exact hR
private theorem sv (a b : ℕ) : V a b = c*sqrt ((b:ℝ)+1)*A a (b+1) := by
  cases a with
  | zero => exact sv0 b
  | succ a =>
    have hi := q_intParts a b
    rw [sb] at hi
    apply mul_left_cancel₀ (a:=sqrt ((a:ℝ)+1)) (by positivity)
    convert hi using 1 <;> ring
private theorem csq : c^2 = Real.pi/2 := by
  have h1 : d^2=2*Real.pi := Real.sq_sqrt (by positivity)
  unfold c
  rw [div_pow,h1]
  field_simp [Real.pi_ne_zero]
private theorem polyInt (p : ℤ[X]) : Integrable (fun x : ℝ => aeval x p) γ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add,Pi.add_def] using! hp.add hq
  | monomial n a =>
    have hi : Integrable (fun x : ℝ => x^n) γ :=
      integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
        (by simp [γ,integrableExpSet_fun_id_gaussianReal]) n
    simpa only [aeval_monomial] using hi.const_mul ((algebraMap ℤ ℝ) a)
private theorem hfI (b : ℕ) : Integrable (h b) γ := (polyInt (hermite b)).div_const _
private theorem hfUI (b : ℕ) : Integrable (fun x => U1 x*h b x) γ := by
  apply (((polyInt ((Polynomial.X^2-1)*hermite b)).div_const (sf b)).const_mul (3*slope)).congr
  apply ae_of_all
  intro x
  simp only [U1,h,QuadSDE.hermiteN,map_mul,map_sub,map_pow,aeval_X,map_one,sf]; ring
private theorem hct (b : ℕ) : Continuous (h b) := by unfold h QuadSDE.hermiteN; fun_prop
private theorem rct (r : ℝ) : Continuous (fun p : ℝ×ℝ => R r (U p.1) (U p.2)) := by unfold R U; fun_prop
private theorem r_bound (r u v : ℝ) (hr : |r| < 1) : |R r u v| ≤ (1-r^2)^(-(1:ℝ)/2) := by
  have hd := denpos r hr
  have hn : 0 ≤ u^2-2*r*u*v+v^2 := by nlinarith only [sq_nonneg (u-r*v),mul_nonneg hd.le (sq_nonneg v)]
  unfold R
  rw [abs_of_nonneg (mul_nonneg (rpow_nonneg hd.le _) (exp_nonneg _))]
  apply mul_le_of_le_one_right (rpow_nonneg hd.le _)
  apply exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hn) (by positivity)
private def K (r : ℝ) (f : ℝ → ℝ) (p : ℝ×ℝ) := R r (U p.1) (U p.2)*(f p.1*f p.2)
private theorem kIntegrable {r : ℝ} (hr : |r| < 1) (f : ℝ → ℝ) (hf : Continuous f) (hi : Integrable f γ) :
    Integrable (K r f) (γ.prod γ) := by
  have hc : Continuous (K r f) := (rct r).mul ((hf.comp continuous_fst).mul (hf.comp continuous_snd))
  apply Integrable.mono' ((hi.abs.mul_prod hi.abs).const_mul ((1-r^2)^(-(1:ℝ)/2))) hc.aestronglyMeasurable
  apply ae_of_all
  intro p
  simp only [K,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_right (r_bound r _ _ hr) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
private theorem weightedSeries (r : ℝ) (hr : |r| < 1/4) (f : ℝ → ℝ) (hf : Continuous f) (hi : Integrable f γ) :
    HasSum (fun a : ℕ => r^a*(∫ x : ℝ, Q a (U x)*f x ∂γ)^2) (∫ p : ℝ×ℝ, K r f p ∂γ.prod γ) := by
  let b (p : ℝ×ℝ) := 4*(|f p.1| * |f p.2|)
  let g (a : ℕ) (p : ℝ×ℝ) := (r^a*Q a (U p.1)*Q a (U p.2))*(f p.1*f p.2)
  let r' := 4*|r|
  have hr' : 0 ≤ r' := mul_nonneg (by norm_num) (abs_nonneg _)
  have hlt : r' < 1 := by dsimp [r']; linarith
  have ht := summable_geometric_of_lt_one hr' hlt
  have hib : Integrable b (γ.prod γ) := (hi.abs.mul_prod hi.abs).const_mul 4
  have hb (a : ℕ) (p : ℝ×ℝ) : ‖g a p‖ ≤ r'^a*b p := by
    have hq := mul_le_mul (boundQ a (U p.1)) (boundQ a (U p.2)) (abs_nonneg _) (by positivity)
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (show 0 ≤ |r| ^a by positivity))
      (mul_nonneg (abs_nonneg (f p.1)) (abs_nonneg (f p.2)))
    simp only [g,b,r',Real.norm_eq_abs,abs_mul,abs_pow,mul_pow]
    calc _ = |r| ^a*(|Q a (U p.1)| * |Q a (U p.2)|)*(|f p.1| * |f p.2|) := by ring
         _ ≤ _ := h
         _ = _ := by rw [show (4:ℝ)^a = 2^a*2^a by rw [← mul_pow]; norm_num]; ring
  have qu (a : ℕ) : Continuous (fun t : ℝ => Q a (U t)) := (q_cont a).comp (by unfold U; fun_prop)
  have gc (a : ℕ) : Continuous (g a) := ((continuous_const.mul ((qu a).comp continuous_fst)).mul ((qu a).comp continuous_snd)).mul ((hf.comp continuous_fst).mul (hf.comp continuous_snd))
  have hh := hasSum_integral_of_dominated_convergence (μ:=γ.prod γ) (F:=g) (f:=K r f)
    (fun a p => r'^a*b p)
    (fun a => (gc a).aestronglyMeasurable)
    (fun a => ae_of_all _ (hb a))
    (ae_of_all _ (fun p => ht.mul_right (b p)))
    (by simp_rw [tsum_mul_right]; exact hib.const_mul _)
    (ae_of_all _ (fun p => (qSeries r (U p.1) (U p.2) (by linarith : |r| < 1)).mul_right (f p.1*f p.2)))
  apply hh.congr_fun
  intro a
  let q (x : ℝ) := Q a (U x)*f x
  have e (p : ℝ×ℝ) : g a p = r^a*(q p.1*q p.2) := by unfold g q; ring
  simp only [e,integral_const_mul]
  rw [integral_prod_mul q q]
  simp only [q,pow_two]
private def rR (t : ℝ) := (t-0.34101124^2*t^3+0.05276111^2*t^5)/(1+0.34101124^2+0.05276111^2)
private def rE (t : ℝ) := (t-3*0.34101124^2*t^3+5*0.05276111^2*t^5)/(1+0.34101124^2+0.05276111^2)
private theorem rho_real (t : ℝ) : rho (t:ℂ) = Complex.ofReal (rR t) := by norm_num [rho,rR]
private theorem rhoEuler_real (t : ℝ) : rhoEuler (t:ℂ) = Complex.ofReal (rE t) := by norm_num [rhoEuler,rE]
private theorem density_real (r u v : ℝ) (hr : |r| < 1) : density (r:ℂ) (u:ℂ) (v:ℂ) = Complex.ofReal (R r u v) := by
  have hd := denpos r hr
  have he := Complex.ofReal_cpow hd.le (1/2)
  push_cast at he
  rw [density,← he,R,show -(1:ℝ)/2=-(1/2) by ring,Real.rpow_neg hd.le]
  push_cast; ring
private def mode (t : ℝ) (b : ℕ) := ∫ x : ℝ, ∫ y : ℝ, phiOne (t:ℂ) x y *
    Complex.ofReal (h b x*h b y) ∂γ ∂γ
private theorem mode_eq (t : ℝ) (hr : |rR t| < 1) (b : ℕ) :
    mode t b = Complex.ofReal (rE t*(∫ p, K (rR t) (h b) p ∂γ.prod γ) -
      t*(∫ p, K (rR t) (fun x => U1 x*h b x) p ∂γ.prod γ)) := by
  have hu : Continuous (fun x => U1 x*h b x) := (show Continuous U1 by unfold U1; fun_prop).mul (hct b)
  have hi := kIntegrable hr (h b) (hct b) (hfI b)
  have hj := kIntegrable hr _ hu (hfUI b)
  let k (p : ℝ×ℝ) := rE t*K (rR t) (h b) p-t*K (rR t) (fun x => U1 x*h b x) p
  have hh : Integrable k (γ.prod γ) := (hi.const_mul _).sub (hj.const_mul _)
  rw [← integral_const_mul,← integral_const_mul,← integral_sub (hi.const_mul _) (hj.const_mul _)]
  change _ = Complex.ofReal (∫ p, k p ∂γ.prod γ)
  rw [integral_prod _ hh,← integral_complex_ofReal]
  unfold mode
  apply integral_congr_ae; apply ae_of_all; intro x
  change _ = Complex.ofReal (∫ y, k (x,y) ∂γ)
  rw [← integral_complex_ofReal]
  apply integral_congr_ae; apply ae_of_all; intro y
  simp only [phiOne,rho_real,rhoEuler_real,k,K,threshold,thresholdDeriv]
  change (↑(rE t)-(t:ℂ)*↑(U1 x)*↑(U1 y))*density (rR t) (U x) (U y)*↑(h b x*h b y) = _
  rw [density_real _ _ _ hr]; push_cast; ring
private theorem mode_series (t : ℝ) (hr : |rR t| < 1/4) (b : ℕ) :
    HasSum (fun a : ℕ => Complex.ofReal (Real.pi/2 *
      (rE t*((a:ℝ)+1)*A (a+1) b^2 - t*((b:ℝ)+1)*A a (b+1)^2)*(rR t)^a)) (mode t b) := by
  have hu : Continuous (fun x => U1 x*h b x) := (show Continuous U1 by unfold U1; fun_prop).mul (hct b)
  have b1 := weightedSeries _ hr _ (hct b) (hfI b)
  have b2 := weightedSeries _ hr _ hu (hfUI b)
  have hw : ∀ a : ℕ, (∫ x : ℝ, Q a (U x)*(U1 x*h b x) ∂γ) = V a b := by
    intro a
    apply integral_congr_ae; apply ae_of_all; intro x; dsimp only; ring
  rw [mode_eq t (by linarith : |rR t| < 1) b]
  apply Complex.ofRealCLM.hasSum
  apply ((b1.mul_left (rE t)).sub (b2.mul_left t)).congr_fun
  intro a
  change (Real.pi/2*(rE t*((a:ℝ)+1)*A (a+1) b^2-t*((b:ℝ)+1)*A a (b+1)^2)*(rR t)^a : ℝ) = rE t*((rR t)^a*B a b^2)-t*((rR t)^a*_ ^2)
  rw [hw,sb,sv]
  simp only [mul_pow,csq,Real.sq_sqrt (show 0 ≤ (a:ℝ)+1 by positivity),
    Real.sq_sqrt (show 0 ≤ (b:ℝ)+1 by positivity)]
  ring
private def k (a b : ℕ) : ℂ := Complex.ofReal (Real.pi/2*A a b^2)
private def W (p : ℕ×ℕ) (z : ℂ) := k p.1 p.2*rho z^p.1*(-z)^p.2
private def G (z : ℂ) := ∑' p : ℕ×ℕ, W p z
private def primary (z : ℂ) (p : ℕ×ℕ) :=
  rhoEuler z*(k (p.1+1) p.2*((p.1:ℂ)+1)*rho z^p.1*(-z)^p.2)
private def secondary (z : ℂ) (p : ℕ×ℕ) :=
  (-z)*(k p.1 (p.2+1)*((p.2:ℂ)+1)*rho z^p.1*(-z)^p.2)
private def shA (f : ℕ×ℕ → ℂ) : ℕ×ℕ → ℂ
  | (0,_) => 0
  | (a+1,b) => f (a,b)
private def shB (f : ℕ×ℕ → ℂ) : ℕ×ℕ → ℂ
  | (_,0) => 0
  | (a,b+1) => f (a,b)
private theorem shiftA_sum {f : ℕ×ℕ → ℂ} {v : ℂ} (hf : HasSum f v) : HasSum (shA f) v := by
  let i (p : ℕ×ℕ) := (p.1+1,p.2)
  have hi : Function.Injective i := by rintro ⟨a,b⟩ ⟨c,d⟩; simp [i]
  apply (hi.hasSum_iff (f:=shA f) (fun p hp => ?_)).mp
  · exact hf
  · rcases p with ⟨_|a,b⟩
    · rfl
    · exact False.elim (hp ⟨(a,b),rfl⟩)
private theorem shiftB_sum {f : ℕ×ℕ → ℂ} {v : ℂ} (hf : HasSum f v) : HasSum (shB f) v := by
  let i (p : ℕ×ℕ) := (p.1,p.2+1)
  have hi : Function.Injective i := by rintro ⟨a,b⟩ ⟨c,d⟩; simp [i]
  apply (hi.hasSum_iff (f:=shB f) (fun p hp => ?_)).mp
  · exact hf
  · rcases p with ⟨a,_|b⟩
    · rfl
    · exact False.elim (hp ⟨(a,b),rfl⟩)
private theorem norm_rho {z : ℂ} {R : ℝ} (hR : R ≤ 1) (hz : ‖z‖ ≤ R) : ‖rho z‖ ≤ R := by
  let a : ℝ := 0.34101124^2
  let b : ℝ := 0.05276111^2
  let V : ℝ := 1+a+b
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hV : 0 < V := by dsimp [V]; positivity
  have he : rho z = (z-(a:ℂ)*z^3+(b:ℂ)*z^5)/(V:ℂ) := by norm_num [rho,V,a,b]
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV,div_le_iff₀ hV]
  calc
    _ ≤ (‖z‖+‖(a:ℂ)*z^3‖)+‖(b:ℂ)*z^5‖ :=
      (norm_add_le ..).trans (add_le_add_left (norm_sub_le ..) _)
    _ ≤ R*V := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,V]
      have hh : ‖z‖ ≤ 1 := hz.trans hR
      have h3 : ‖z‖^3 ≤ R := (pow_le_of_le_one (norm_nonneg _) hh (by decide : 3 ≠ 0)).trans hz
      have h5 : ‖z‖^5 ≤ R := (pow_le_of_le_one (norm_nonneg _) hh (by decide : 5 ≠ 0)).trans hz
      nlinarith only [hz,mul_le_mul_of_nonneg_left h3 ha,mul_le_mul_of_nonneg_left h5 hb]
private theorem k2 (a b : ℕ) : ‖k a b‖ ≤ 2 := by
  have h := (cq_gaussian_hermite_expansion 0.136419125 0.34101124 0.05276111).2 a b
  change |A a b| ≤ 1 at h
  have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs,one_pow] at hs
  rw [k,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ Real.pi/2 by positivity)
  linarith only [hb,Real.pi_lt_four]
private def bb (n : ℕ) := ((n:ℝ)+1)*(1/2:ℝ)^n
private theorem bsum : Summable bb := by
  have hg := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num [Real.norm_eq_abs] : ‖(1/2:ℝ)‖ < 1)
  exact (h1.add hg).congr (fun n => by simp only [bb,pow_one]; ring)
private def major (p : ℕ×ℕ) := bb p.1*bb p.2
private theorem majorSum : Summable major := bsum.mul_of_nonneg bsum (fun n => by unfold bb; positivity) (fun n => by unfold bb; positivity)
private theorem boundW (z : ℂ) (hz : ‖z‖ ≤ 1/2) (p : ℕ×ℕ) :
    ‖W p z‖ ≤ 2*major p ∧ ‖primary z p‖ ≤ (‖rhoEuler z‖*2)*major p ∧
      ‖secondary z p‖ ≤ (‖z‖*2)*major p := by
  have hr := norm_rho (by norm_num) hz
  have up (i : ℕ) : ‖rho z‖^i ≤ (1/2:ℝ)^i := pow_le_pow_left₀ (norm_nonneg _) hr i
  have vp (i : ℕ) : ‖z‖^i ≤ (1/2:ℝ)^i := pow_le_pow_left₀ (norm_nonneg _) hz i
  have nrm (i : ℕ) : ‖(i:ℂ)+1‖=(i:ℝ)+1 := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  let a := p.1; let b := p.2
  have h1 : (1:ℝ) ≤ (a:ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) a]
  have h2 : (1:ℝ) ≤ (b:ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) b]
  have ratio : ‖rho z‖^a*‖z‖^b ≤ (1/2:ℝ)^a*(1/2:ℝ)^b :=
    mul_le_mul (up a) (vp b) (pow_nonneg (norm_nonneg _) _) (by positivity)
  have bound (i j : ℕ) : ‖k i j‖*(‖rho z‖^a*‖z‖^b) ≤ 2*((1/2:ℝ)^a*(1/2:ℝ)^b) :=
    mul_le_mul (k2 i j) ratio (by positivity) (by norm_num)
  have bound' (i j : ℕ) : ‖k i j‖*(‖rho z‖^a*‖z‖^b) ≤ 2*major p := by
    apply (bound i j).trans
    dsimp [major,bb,a,b]
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by norm_num) (by positivity))
      (show 0 ≤ (1/2:ℝ)^p.1*(1/2:ℝ)^p.2 by positivity)]
  simp only [W,primary,secondary,norm_mul,norm_pow,norm_neg,nrm]
  constructor
  · simpa only [a,b,mul_assoc] using bound' a b
  constructor
  · rw [mul_assoc ‖rhoEuler z‖]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hh := mul_le_mul_of_nonneg_left (bound (a+1) b) (by positivity : 0 ≤ (a:ℝ)+1)
    have extra := mul_le_mul_of_nonneg_right h2 (show (0:ℝ) ≤ 2*((a:ℝ)+1)*((1/2:ℝ)^a*(1/2:ℝ)^b) by positivity)
    dsimp only [major,bb]; change _ ≤ 2*(((a:ℝ)+1)*(1/2)^a*(((b:ℝ)+1)*(1/2)^b))
    change ‖k (a+1) b‖*((a:ℝ)+1)*‖rho z‖^a*‖z‖^b ≤ _
    nlinarith only [hh,extra]
  · rw [mul_assoc ‖z‖]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hh := mul_le_mul_of_nonneg_left (bound a (b+1)) (by positivity : 0 ≤ (b:ℝ)+1)
    have extra := mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ 2*((b:ℝ)+1)*((1/2:ℝ)^a*(1/2:ℝ)^b) by positivity)
    dsimp only [major,bb]; change _ ≤ 2*(((a:ℝ)+1)*(1/2)^a*(((b:ℝ)+1)*(1/2)^b))
    change ‖k a (b+1)‖*((b:ℝ)+1)*‖rho z‖^a*‖z‖^b ≤ _
    nlinarith only [hh,extra]
private theorem rD (z : ℂ) : DifferentiableAt ℂ rho z := by unfold rho; fun_prop
private theorem rhoED (z : ℂ) : z*deriv rho z = rhoEuler z := by
  let a : ℂ := 0.34101124^2
  let b : ℂ := 0.05276111^2
  let V := 1+a+b
  have hr : HasDerivAt rho ((1-a*(3*z^2)+b*(5*z^4))/V) z := by
    apply ((((hasDerivAt_id z).sub ((hasDerivAt_pow 3 z).const_mul a)).add ((hasDerivAt_pow 5 z).const_mul b)).div_const V).congr_deriv
    norm_num
  rw [hr.deriv]
  dsimp [a,b,V,rhoEuler]; ring
private theorem dW (p : ℕ×ℕ) (z : ℂ) : DifferentiableAt ℂ (W p) z := by
  unfold W; exact ((differentiableAt_const _).mul ((rD z).pow _)).mul (differentiableAt_id.neg.pow _)
private theorem termDW (p : ℕ×ℕ) (z : ℂ) :
    z*deriv (W p) z=shA (primary z) p+shB (secondary z) p := by
  rcases p with ⟨a,b⟩
  have hd := ((((rD z).hasDerivAt.pow a).const_mul (k a b)).mul ((hasDerivAt_id z).neg.pow b)).deriv
  change deriv (W (a,b)) z =
    ((k a b)*((a:ℂ)*rho z^(a-1)*deriv rho z))*(-z)^b +
      ((k a b)*rho z^a)*((b:ℂ)*(-z)^(b-1)*(-1)) at hd
  rw [hd]
  cases a <;> cases b <;>
    simp only [shA,shB,primary,secondary,← rhoED,pow_zero,Nat.cast_zero,Nat.cast_succ,Nat.succ_sub_succ_eq_sub,Nat.sub_zero,pow_succ] <;> ring
private theorem onDisk (z : ℂ) (hz : ‖z‖ < 1/2) :
    DifferentiableAt ℂ G z ∧ z*deriv G z = (∑' p, primary z p)+(∑' p, secondary z p) := by
  let B := Metric.ball (0:ℂ) (1/2)
  have hB : z ∈ B := by simpa [B,Metric.mem_ball] using hz
  have hW (p : ℕ×ℕ) (w : ℂ) (hw : w ∈ B) : ‖W p w‖ ≤ 2*major p :=
    (boundW _ (by simpa [B,Metric.mem_ball] using hw : ‖w‖ < 1/2).le _).1
  have hdiff (p : ℕ×ℕ) : DifferentiableOn ℂ (W p) B := fun w _ => (dW p w).differentiableWithinAt
  have hder := Complex.hasSum_deriv_of_summable_norm (majorSum.mul_left 2) hdiff Metric.isOpen_ball hW hB
  have h1 : Summable (primary z) := (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => (boundW z hz.le p).2.1) (majorSum.mul_left (‖rhoEuler z‖*2))).of_norm
  have h2 : Summable (secondary z) := (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => (boundW z hz.le p).2.2) (majorSum.mul_left (‖z‖*2))).of_norm
  exact ⟨(Complex.differentiableOn_tsum_of_summable_norm (majorSum.mul_left 2) hdiff Metric.isOpen_ball hW).differentiableAt (Metric.isOpen_ball.mem_nhds hB),
    (hder.mul_left z).unique (((shiftA_sum h1.hasSum).add (shiftB_sum h2.hasSum)).congr_fun (fun p => termDW p z))⟩
private def Hcorr := cqCorr 0.136419125 0.34101124 0.05276111
private theorem gReal (t : ℝ) (ht : |t| < 1) : G (t:ℂ) = Complex.ofReal (Hcorr t) := by
  have hh := Complex.ofRealCLM.hasSum ((cq_gaussian_hermite_expansion 0.136419125 0.34101124 0.05276111).1 t ht)
  have e : (cqRhoPoly 0.34101124 0.05276111).eval t = rR t := by
    simp only [cqRhoPoly,eval_mul,eval_sub,eval_add,eval_C,eval_pow,eval_X,rR]
    ring
  apply HasSum.tsum_eq (f:=fun p : ℕ×ℕ => W p (t:ℂ))
  apply hh.congr_fun
  intro p
  simp only [W,k,A,Complex.ofRealCLM_apply,e,rho_real]
  push_cast; ring
private theorem realTrace (t : ℝ) (ht : |t| < 1/8) :
    (∑' b : ℕ, (-(t:ℂ))^b*mode t b) = (t:ℂ)*deriv G (t:ℂ) := by
  have hz : ‖(t:ℂ)‖ < 1/2 := by rw [Complex.norm_real,Real.norm_eq_abs]; linarith
  have hr : |rR t| < 1/4 := by
    have h1 := norm_rho (z:=(t:ℂ)) (R:=1/8) (by norm_num) (by simpa only [Complex.norm_real,Real.norm_eq_abs] using ht.le)
    rw [rho_real,Complex.norm_real,Real.norm_eq_abs] at h1
    linarith
  have h1 : Summable (primary (t:ℂ)) := (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => (boundW _ hz.le p).2.1) (majorSum.mul_left _)).of_norm
  have h2 : Summable (secondary (t:ℂ)) := (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => (boundW _ hz.le p).2.2) (majorSum.mul_left _)).of_norm
  have hh := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (h1.hasSum.add h2.hasSum)
  have rows (b : ℕ) : HasSum (fun a : ℕ => primary (t:ℂ) (a,b)+secondary (t:ℂ) (a,b)) ((-(t:ℂ))^b*mode t b) := by
    apply ((mode_series t hr b).mul_left ((-(t:ℂ))^b)).congr_fun
    intro a
    simp only [primary,secondary,k,rho_real,rhoEuler_real]
    push_cast; ring
  rw [(onDisk _ hz).2]
  exact (hh.prod_fiberwise rows).tsum_eq
private theorem price :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (fun t : ℝ => ∑' n : ℕ, (-(t:ℂ))^n * (∫ x : ℝ, ∫ y : ℝ,
      CQBoundary.phiOne (t:ℂ) x y * Complex.ofReal (QuadSDE.hermiteN n x * QuadSDE.hermiteN n y)
      ∂gaussianReal 0 1 ∂gaussianReal 0 1)) =ᶠ[𝓝 0] fun t : ℝ => Complex.ofReal (t*deriv H t) := by
  have near : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1/8 := (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
  filter_upwards [near] with t ht
  have hz : ‖(t:ℂ)‖ < 1/2 := by rw [Complex.norm_real,Real.norm_eq_abs]; linarith
  have hd := (onDisk _ hz).1.hasDerivAt.comp_ofReal
  have he : (fun u : ℝ => G (u:ℂ)) =ᶠ[𝓝 t] fun u => Complex.ofReal (Hcorr u) := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds (show |t| < 1 by linarith)] with u hu using gReal u hu
  have heR : Hcorr =ᶠ[𝓝 t] fun u : ℝ => (G (u:ℂ)).re :=
    he.mono (fun u h => by simpa only [Complex.ofReal_re] using (congrArg Complex.re h).symm)
  have dh : DifferentiableAt ℝ Hcorr t :=
    (Complex.reCLM.differentiableAt.comp t hd.differentiableAt).congr_of_eventuallyEq heR
  have hid : deriv G (t:ℂ) = Complex.ofReal (deriv Hcorr t) :=
    hd.deriv.symm.trans (he.deriv_eq.trans dh.hasDerivAt.ofReal_comp.deriv)
  change (∑' b : ℕ, (-(t:ℂ))^b*mode t b) = Complex.ofReal (t*deriv Hcorr t)
  rw [realTrace t ht,hid,Complex.ofReal_mul]

end PriceCoefficients

open PriceCoefficients in
theorem solution :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (fun t : ℝ => ∑' n : ℕ, (-(t:ℂ))^n * (∫ x : ℝ, ∫ y : ℝ,
      CQBoundary.phiOne (t:ℂ) x y * Complex.ofReal (QuadSDE.hermiteN n x * QuadSDE.hermiteN n y)
      ∂gaussianReal 0 1 ∂gaussianReal 0 1)) =ᶠ[𝓝 0] fun t : ℝ => Complex.ofReal (t*deriv H t) := price
