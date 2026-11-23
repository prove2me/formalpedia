-- Prove2me | solution 1 for GrothendieckLB.Supplement.gaussian_hermite_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T19:55:39.832364+00:00
-- url     : https://prove2.me/submissions/7e345c1b-3619-43ba-b3da-bc63b848d82b

import Definitions.Def_QuadSDE_GaussHermite
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib

open Real Polynomial MeasureTheory ProbabilityTheory
set_option maxHeartbeats 1000000

namespace HermiteIntegration
set_option maxHeartbeats 800000

private noncomputable def wgt (x : ℝ) := Real.exp (-(x^2)/2)
private noncomputable def mon (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n)

private theorem int_poly (p : ℤ[X]) : Integrable fun x : ℝ => aeval x p*wgt x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hi : Integrable (fun x : ℝ => aeval x p*wgt x+aeval x q*wgt x) := hp.add hq
    simpa only [map_add,add_mul] using hi
  | monomial n a =>
    have h : Integrable fun x : ℝ => x^n * exp (-(1/2:ℝ)*x^2) := by
      simpa only [rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
        (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg n))
    convert h.const_mul ((algebraMap ℤ ℝ) a) using 1
    ext x; rw [aeval_monomial]; dsimp only [wgt]; ring_nf

private theorem deriv_weighted (n : ℕ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => mon n u*wgt u) (-(mon (n+1) x*wgt x)) x := by
  have hw : HasDerivAt wgt ((-x)*wgt x) x := by
    apply ((((hasDerivAt_pow 2 x).neg).div_const 2).exp).congr_deriv
    dsimp [wgt]; ring
  apply (((hermite n).hasDerivAt_aeval x).mul hw).congr_deriv
  simp only [mon,hermite_succ,map_sub,map_mul,aeval_X]; ring

private theorem cm (n : ℕ) : Continuous (mon n) := by unfold mon; fun_prop
private theorem cw : Continuous wgt := by unfold wgt; fun_prop

private theorem int_bound (f : ℝ → ℂ) (hf : Continuous f) (C : ℝ) (k : ℕ)
    (h : ∀ x : ℝ, ‖f x‖≤C*(1+x^2)^k) (n : ℕ) :
    Integrable (fun x : ℝ => f x*Complex.ofReal (mon n x*wgt x)) := by
  let P : ℤ[X] := (1+X^2)^k*hermite n
  have hv (x : ℝ) : |aeval x P*wgt x|=(1+x^2)^k*|mon n x*wgt x| := by
    simp only [P,map_mul,map_pow,map_add,map_one,aeval_X,mon]
    rw [mul_assoc,abs_mul,abs_of_nonneg (by positivity : 0≤(1+x^2)^k)]
  have hm : Continuous (fun x : ℝ => f x*Complex.ofReal (mon n x*wgt x)) :=
    hf.mul (Complex.continuous_ofReal.comp ((cm n).mul cw))
  apply Integrable.mono' ((int_poly P).abs.const_mul C) hm.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,hv,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h x) (abs_nonneg _)

end HermiteIntegration

open HermiteIntegration in
theorem solution (f g : ℝ → ℂ) (hg : Continuous g) (hd : ∀ x : ℝ, HasDerivAt f (g x) x)
    (C : ℝ) (k : ℕ) (hb : ∀ x : ℝ, ‖f x‖+‖g x‖≤C*(1+x^2)^k) (n : ℕ) :
    (∫ x : ℝ, g x*Complex.ofReal (QuadSDE.hermiteN n x) ∂gaussianReal 0 1) =
      Complex.ofReal (Real.sqrt (n+1:ℝ)) *
        ∫ x : ℝ, f x*Complex.ofReal (QuadSDE.hermiteN (n+1) x) ∂gaussianReal 0 1 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hfi (m : ℕ) := int_bound f hf C k (fun x => (le_add_of_nonneg_right (norm_nonneg _)).trans (hb x)) m
  have hgi (m : ℕ) := int_bound g hg C k (fun x => (le_add_of_nonneg_left (norm_nonneg _)).trans (hb x)) m
  have hp (x : ℝ) : HasDerivAt (fun u : ℝ => f u * Complex.ofReal (mon n u*wgt u))
      (g x*Complex.ofReal (mon n x*wgt x)-f x*Complex.ofReal (mon (n+1) x*wgt x)) x := by
    apply ((hd x).mul (deriv_weighted n x).ofReal_comp).congr_deriv
    simp only [Complex.ofReal_neg]; ring
  have hi := integral_eq_zero_of_hasDerivAt_of_integrable hp ((hgi n).sub (hfi (n+1))) (hfi n)
  rw [integral_sub (hgi n) (hfi (n+1))] at hi
  have he := sub_eq_zero.mp hi
  let a : ℝ := (Real.sqrt (2*Real.pi))⁻¹
  let s (j : ℕ) := Real.sqrt (j.factorial:ℝ)
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x=a*wgt x := by simp [gaussianPDFReal,wgt,a]
  have res (F : ℝ → ℂ) (j : ℕ) :
      (∫ x : ℝ, F x*Complex.ofReal (QuadSDE.hermiteN j x) ∂gaussianReal 0 1) =
      Complex.ofReal (a/s j) * ∫ x : ℝ, F x*Complex.ofReal (mon j x*wgt x) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal)≠0),← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    simp only [Complex.real_smul,hpdf,Complex.ofReal_mul,Complex.ofReal_div]
    change _*(_*Complex.ofReal (mon j x/s j))=_
    push_cast; ring
  rw [res g n,res f (n+1),he,← mul_assoc]
  congr 1
  have hr : s (n+1)=Real.sqrt ((n:ℝ)+1)*s n := by
    dsimp [s]; rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,Real.sqrt_mul (by positivity)]
  rw [hr,← Complex.ofReal_mul]
  congr 1
  have hsq : Real.sqrt ((n:ℝ)+1)≠0 := by positivity
  field_simp [hsq]

