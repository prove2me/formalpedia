-- Prove2me | solution 1 for GrothendieckLB.Supplement.gaussian_hermite_diagonal_bessel
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T19:43:06.804673+00:00
-- url     : https://prove2.me/submissions/76820ed8-c626-4ebe-8a8f-a33ccf17a7ab

import Definitions.Def_QuadSDE_GaussHermite
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib
open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 900000

namespace GaussianHermiteNorm
open Real Set Polynomial MeasureTheory ProbabilityTheory Filter
open scoped Topology
private noncomputable def weight (x : ℝ) := exp (-(x^2)/2)
private noncomputable def herm (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n)
private noncomputable def hg (n : ℕ) (x : ℝ) : ℝ := herm n x*weight x
private theorem poly_integrable (p : ℤ[X]) :
    Integrable fun x : ℝ => aeval x p * weight x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hi : Integrable (fun x : ℝ => aeval x p * weight x + aeval x q * weight x) := hp.add hq
    simpa only [map_add,add_mul] using hi
  | monomial n a =>
    have h : Integrable fun x : ℝ => x^n * exp (-(1/2:ℝ)*x^2) := by
      simpa only [rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
        (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg n))
    convert h.const_mul ((algebraMap ℤ ℝ) a) using 1
    ext x
    rw [aeval_monomial]
    dsimp only [weight]
    ring_nf


private theorem deriv_hg (n : ℕ) (x : ℝ) : HasDerivAt (hg n) (-hg (n+1) x) x := by
  have hw : HasDerivAt weight ((-x)*weight x) x := by
    apply ((((hasDerivAt_pow 2 x).neg).div_const 2).exp).congr_deriv
    dsimp [weight]
    ring
  apply (((hermite n).hasDerivAt_aeval x).mul hw).congr_deriv
  simp only [hg,herm,hermite_succ,map_sub,map_mul,aeval_X]
  ring


private theorem dh (n : ℕ) : derivative (hermite (n+1)) = C ((n+1:ℕ):ℤ)*hermite n := by
  induction n with
  | zero => simp [hermite_succ,hermite_zero]
  | succ n ih =>
    rw [hermite_succ (n+1),ih,derivative_sub,derivative_mul,derivative_X,
      derivative_mul,derivative_C,zero_mul,zero_add,one_mul,ih]
    rw [hermite_succ n]
    push_cast
    simp only [map_add,map_one]
    ring


private theorem deriv_herm (n : ℕ) (x : ℝ) :
    HasDerivAt (herm (n+1)) (((n:ℝ)+1)*herm n x) x := by
  have h := Polynomial.hasDerivAt_aeval (hermite (n+1)) x
  rw [dh] at h
  change HasDerivAt (fun z : ℝ => aeval z (hermite (n+1))) _ x
  simpa only [map_mul,aeval_C,Nat.cast_succ,Nat.cast_add,Nat.cast_one,map_add,map_one,map_natCast,herm] using h

private theorem sq_int (n : ℕ) : Integrable (fun x : ℝ => (herm n x)^2*weight x) := by
  convert poly_integrable ((hermite n)^2) using 1
  ext x
  simp [herm]

private theorem weighted_norm (n : ℕ) :
    (∫ x : ℝ, (herm n x)^2*weight x)=(n.factorial:ℝ)*(∫ x : ℝ, weight x) := by
  induction n with
  | zero => simp [herm,hermite_zero]
  | succ n ih =>
    let f := fun x : ℝ => herm (n+1) x*hg n x
    let d := fun x : ℝ => ((n:ℝ)+1)*((herm n x)^2*weight x)-(herm (n+1) x)^2*weight x
    have hd (x : ℝ) : HasDerivAt f (d x) x := by
      apply ((deriv_herm n x).mul (deriv_hg n x)).congr_deriv
      dsimp [d,hg]
      ring
    have hf : Integrable f := by
      simpa only [f,hg,herm,map_mul,mul_assoc] using poly_integrable (hermite (n+1)*hermite n)
    have hdint : Integrable d := ((sq_int n).const_mul ((n:ℝ)+1)).sub (sq_int (n+1))
    have h := integral_eq_zero_of_hasDerivAt_of_integrable hd hdint hf
    change ∫ x : ℝ, ((n:ℝ)+1)*((herm n x)^2*weight x)-(herm (n+1) x)^2*weight x = 0 at h
    rw [integral_sub ((sq_int n).const_mul _) (sq_int (n+1)),integral_const_mul,ih] at h
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
    linarith only [h]

theorem weighted (n : ℕ) :
    Integrable (fun x : ℝ => QuadSDE.hermiteN n x*gaussianPDFReal 0 1 x) ∧
    (∫ x : ℝ, (QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x)=1 ∧
    (∫ x : ℝ, |QuadSDE.hermiteN n x| *gaussianPDFReal 0 1 x) ≤ 1 := by
  let d : ℝ := (Real.sqrt (2*Real.pi))⁻¹
  let k : ℝ := Real.sqrt (n.factorial:ℝ)
  have hk : k^2=(n.factorial:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hk0 : k ≠ 0 := by dsimp [k]; positivity
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x = d*weight x := by simp [gaussianPDFReal,d,weight]
  have hfirst (x : ℝ) : QuadSDE.hermiteN n x*gaussianPDFReal 0 1 x = (d/k)*(herm n x*weight x) := by
    rw [hpdf]; change (herm n x/k)*(d*weight x)=_; ring
  have hsec (x : ℝ) : (QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x =
      (d/(n.factorial:ℝ))*((herm n x)^2*weight x) := by
    rw [hpdf]; change (herm n x/k)^2*(d*weight x)=_; rw [div_pow,hk]; ring
  have h1 : Integrable (fun x : ℝ => QuadSDE.hermiteN n x*gaussianPDFReal 0 1 x) := by
    simp_rw [hfirst]
    exact (poly_integrable (hermite n)).const_mul _
  have h2 : Integrable (fun x : ℝ => (QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x) := by
    simp_rw [hsec]
    exact (sq_int n).const_mul _
  have hnorm := integral_gaussianPDFReal_eq_one 0 (v:=1) (by norm_num)
  have hpdfint : d*(∫ x : ℝ, weight x)=1 := by
    simpa only [hpdf,integral_const_mul] using hnorm
  have h2val : (∫ x : ℝ, (QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x)=1 := by
    simp_rw [hsec]
    rw [integral_const_mul,weighted_norm]
    calc _ = d*(∫ x : ℝ, weight x) := by field_simp
         _ = 1 := hpdfint
  refine ⟨h1,h2val,?_⟩
  have h1abs : Integrable (fun x : ℝ => |QuadSDE.hermiteN n x| *gaussianPDFReal 0 1 x) := by
    simpa only [abs_mul,abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)] using h1.abs
  have hi := integral_mono (h1abs.const_mul 2) ((integrable_gaussianPDFReal 0 1).add h2)
      (fun x => by
        change 2*(|QuadSDE.hermiteN n x| *gaussianPDFReal 0 1 x) ≤
          gaussianPDFReal 0 1 x+(QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x
        have hsq := sq_nonneg (|QuadSDE.hermiteN n x|-1)
        have hadd : 2*|QuadSDE.hermiteN n x| ≤ 1+(QuadSDE.hermiteN n x)^2 := by
          nlinarith only [hsq,sq_abs (QuadSDE.hermiteN n x)]
        simpa only [mul_assoc,add_mul,one_mul] using
          mul_le_mul_of_nonneg_right hadd (gaussianPDFReal_nonneg _ _ _))
  change (∫ x : ℝ, 2*(|QuadSDE.hermiteN n x| *gaussianPDFReal 0 1 x)) ≤
    ∫ x : ℝ, gaussianPDFReal 0 1 x+(QuadSDE.hermiteN n x)^2*gaussianPDFReal 0 1 x at hi
  rw [integral_const_mul,integral_add (integrable_gaussianPDFReal 0 1) h2,hnorm,h2val] at hi
  linarith only [hi]

private theorem weighted_cross_integrable (m n : ℕ) :
    Integrable fun x : ℝ => herm m x*herm n x*weight x := by
  simpa only [herm,map_mul] using poly_integrable (hermite m*hermite n)

private theorem weighted_offdiag (m n : ℕ) (hne : m < n) :
    (∫ x : ℝ, herm m x*herm n x*weight x)=0 := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      have hder := fun x : ℝ => deriv_hg n x
      have hdint : Integrable fun x : ℝ => -hg (n+1) x := (poly_integrable (hermite (n+1))).neg
      have hf : Integrable (hg n) := poly_integrable (hermite n)
      have eqv := integral_eq_zero_of_hasDerivAt_of_integrable hder hdint hf
      rw [integral_neg] at eqv
      simpa [herm,hermite_zero,hg] using eqv
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n =>
      let f (x : ℝ) := herm (m+1) x*hg n x
      let g (x : ℝ) := ((m:ℝ)+1)*(herm m x*herm n x*weight x)-herm (m+1) x*herm (n+1) x*weight x
      have hh (x : ℝ) : HasDerivAt f (g x) x := by
        apply ((deriv_herm m x).mul (deriv_hg n x)).congr_deriv
        dsimp [g,hg]; ring
      have hf : Integrable f := by simpa only [f,hg,mul_assoc] using weighted_cross_integrable (m+1) n
      have hh' : Integrable g := ((weighted_cross_integrable m n).const_mul _).sub (weighted_cross_integrable _ _)
      have eqv := integral_eq_zero_of_hasDerivAt_of_integrable hh hh' hf
      change (∫ x : ℝ, ((m:ℝ)+1)*(herm m x*herm n x*weight x)-herm (m+1) x*herm (n+1) x*weight x)=0 at eqv
      rw [integral_sub ((weighted_cross_integrable m n).const_mul _) (weighted_cross_integrable _ _),
        integral_const_mul,ih n (by omega)] at eqv
      linarith only [eqv]

private theorem law (m n : ℕ) :
    Integrable (fun x : ℝ => QuadSDE.hermiteN m x*QuadSDE.hermiteN n x) (gaussianReal 0 1) ∧
    (∫ x : ℝ, QuadSDE.hermiteN m x*QuadSDE.hermiteN n x ∂gaussianReal 0 1) = if m=n then 1 else 0 := by
  let d := (Real.sqrt (2*Real.pi))⁻¹
  let k (j : ℕ) := Real.sqrt (j.factorial:ℝ)
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x=d*weight x := by
    simp [gaussianPDFReal,weight,d]
  have hmul (x : ℝ) : gaussianPDFReal 0 1 x * (QuadSDE.hermiteN m x*QuadSDE.hermiteN n x)=
      (d/(k m*k n))*(herm m x*herm n x*weight x) := by
    rw [hpdf]; change _*(herm m x/k m*(herm n x/k n))=_; ring
  have h1 : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * (QuadSDE.hermiteN m x*QuadSDE.hermiteN n x)) := by
    simp_rw [hmul]; exact (weighted_cross_integrable m n).const_mul _
  constructor
  · rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1:NNReal)≠0)]
    rw [integrable_withDensity_iff_integrable_smul₀' (measurable_gaussianPDF _ _).aemeasurable
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
    simpa only [toReal_gaussianPDF,smul_eq_mul] using h1
  · rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal)≠0)]
    simp only [smul_eq_mul]
    by_cases h : m=n
    · subst n; rw [if_pos rfl]
      simpa only [← sq,mul_comm (gaussianPDFReal 0 1 _) _] using (weighted m).2.1
    · rw [if_neg h]; simp_rw [hmul]; rw [integral_const_mul]
      suffices (∫ x : ℝ, herm m x*herm n x*weight x)=0 by rw [this,mul_zero]
      rcases lt_or_gt_of_ne h with hmn|hnm
      · exact weighted_offdiag m n hmn
      · simpa only [mul_comm (herm m _) (herm n _)] using weighted_offdiag n m hnm


private noncomputable abbrev γ : Measure ℝ := gaussianReal 0 1
private noncomputable def pairH (n : ℕ) (p : ℝ×ℝ) : ℂ :=
  Complex.ofReal (QuadSDE.hermiteN n p.1 * QuadSDE.hermiteN n p.2)

private theorem pairLp (n : ℕ) : MemLp (pairH n) 2 (γ.prod γ) := by
  have hm : Continuous (pairH n) := by unfold pairH QuadSDE.hermiteN; fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  have H := (law n n).1
  have hEq (p : ℝ×ℝ) : ‖pairH n p‖^2=(QuadSDE.hermiteN n p.1*QuadSDE.hermiteN n p.1)*(QuadSDE.hermiteN n p.2*QuadSDE.hermiteN n p.2) := by
    rw [pairH,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,pow_two,pow_two]
  simp_rw [hEq]
  exact H.mul_prod H

private noncomputable def vec (n : ℕ) : Lp ℂ 2 (γ.prod γ) := (pairLp n).toLp _
private theorem hilbert_orthonormal : Orthonormal ℂ vec := by
  rw [orthonormal_iff_ite]
  intro m n
  have hx := (pairLp m).coeFn_toLp
  have hy := (pairLp n).coeFn_toLp
  rw [MeasureTheory.L2.inner_def]
  calc
    _ = ∫ p : ℝ×ℝ, (Complex.ofReal (QuadSDE.hermiteN m p.1*QuadSDE.hermiteN n p.1)) *
        (Complex.ofReal (QuadSDE.hermiteN m p.2*QuadSDE.hermiteN n p.2)) ∂γ.prod γ := by
      apply integral_congr_ae
      filter_upwards [hx,hy] with p h₁ h₂
      change inner ℂ ((pairLp m).toLp _ p) ((pairLp n).toLp _ p)=_
      rw [h₁,h₂]
      simp only [pairH,RCLike.inner_apply,Complex.conj_ofReal,Complex.ofReal_mul,map_mul]
      ring
    _ = _ := by
      let G (x : ℝ) : ℂ := Complex.ofReal (QuadSDE.hermiteN m x*QuadSDE.hermiteN n x)
      change (∫ p : ℝ×ℝ, G p.1*G p.2 ∂γ.prod γ)=_
      rw [integral_prod_mul G G]
      simp only [G,integral_complex_ofReal]
      change (Complex.ofReal (∫ x : ℝ, _ ∂gaussianReal 0 1))*(Complex.ofReal (∫ x : ℝ, _ ∂gaussianReal 0 1))=_
      rw [(law m n).2]
      split <;> norm_num

end GaussianHermiteNorm

open GaussianHermiteNorm in
theorem solution (f : ℝ×ℝ → ℂ) (hf : MemLp f 2 ((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (S : Finset ℕ) :
    (∑ n ∈ S, ‖∫ p : ℝ×ℝ, f p * Complex.ofReal (QuadSDE.hermiteN n p.1*QuadSDE.hermiteN n p.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))‖^2) ≤
      ∫ p : ℝ×ℝ, ‖f p‖^2 ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let F := hf.toLp f
  have hb := hilbert_orthonormal.sum_inner_products_le (s:=S) F
  have hinner (n : ℕ) : inner ℂ (vec n) F = ∫ p, f p * pairH n p ∂γ.prod γ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(pairLp n).coeFn_toLp,hf.coeFn_toLp] with p h₁ h₂
    change inner ℂ ((pairLp n).toLp _ p) (hf.toLp _ p)=_
    rw [h₁,h₂,RCLike.inner_apply]
    simp [pairH]
  have hnorm : ‖F‖^2=∫ p, ‖f p‖^2 ∂γ.prod γ := by
    have he := @inner_self_eq_norm_sq_to_K ℂ _ _ _ _ F
    rw [MeasureTheory.L2.inner_def] at he
    change _ = (Complex.ofReal ‖F‖)^2 at he
    rw [← Complex.ofReal_pow] at he
    have hi : (∫ p, inner ℂ (F p) (F p) ∂γ.prod γ) = Complex.ofReal (∫ p, ‖f p‖^2 ∂γ.prod γ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with p h
      change inner ℂ (hf.toLp _ p) (hf.toLp _ p)=_
      rw [h,inner_self_eq_norm_sq_to_K]
      norm_cast
    exact Complex.ofReal_inj.mp (hi.symm.trans he).symm
  simp only [hinner,hnorm] at hb
  exact hb

