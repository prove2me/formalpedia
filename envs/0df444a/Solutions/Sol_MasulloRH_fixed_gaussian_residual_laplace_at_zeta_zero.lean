-- Prove2me | solution 1 for MasulloRH.fixed_gaussian_residual_laplace_at_zeta_zero
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:23:43.51639+00:00
-- url     : https://prove2.me/submissions/a5bc76a4-b1d0-4d67-8d37-9c559368456b

import Theorems.Thm_MasulloRH_dyadic_gaussian_theta_mellin
import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/- The logarithmic Mellin substitution and Gaussian integral follow the accepted rectangle proof. The conclusion retains the exact transform of the fixed pulse at every ordinate.
https://prove2.me/submissions/5b2cbfbc-22d8-4073-bb0e-dbecd2699cb3 -/

open MeasureTheory Set MasulloRH.GaussianApproximation

private theorem theta_eval (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (hz : riemannZeta s = 0) (y : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (s*x) * theta (x-y)) ∧
    (∫ x : ℝ, Complex.exp (s*x) * theta (x-y)) = 0 := by
  obtain ⟨g,hg,_,_,hm,_⟩ := MasulloRH.dyadic_gaussian_theta_mellin
  let F (t : ℝ) := ∑' j : ℤ, g ((j:ℝ)*t)
  have hmel : HasMellin F s 0 := ⟨(hm s hs hs').1.1,(hm s hs hs').2.1.mpr hz⟩
  have hlog (x : ℝ) : |Real.exp x| • (((Real.exp x:ℝ):ℂ)^(s-1) • F (Real.exp x)) =
      Complex.exp (s*x)*theta x := by
    rw [abs_of_pos (Real.exp_pos _),Complex.real_smul,smul_eq_mul,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp,Complex.ofReal_exp,←mul_assoc,←Complex.exp_add]
    have e : F (Real.exp x)=theta x := by simp only [F,theta,hg]
    rw [e]
    congr 2
    ring
  unfold HasMellin MellinConvergent mellin at hmel
  have hd (x : ℝ) (_ : x ∈ (univ : Set ℝ)) := (Real.hasDerivAt_exp x).hasDerivWithinAt (s:=univ)
  rw [← show Real.exp '' (univ : Set ℝ)=Ioi 0 by rw [image_univ,Real.range_exp],
      integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn,
      integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn] at hmel
  simp only [integrableOn_univ,setIntegral_univ,hlog] at hmel
  let f (x : ℝ) := Complex.exp (s*x)*theta x
  have hshift (x : ℝ) : Complex.exp (s*x)*theta (x-y)=Complex.exp (s*y)*f (x-y) := by
    dsimp only [f]
    rw [←mul_assoc,←Complex.exp_add]
    push_cast
    congr 2
    ring
  simp_rw [hshift]
  refine ⟨(hmel.1.comp_sub_right y).const_mul _,?_⟩
  rw [integral_const_mul,integral_sub_right_eq_self]
  change _ * (∫ x : ℝ, Complex.exp (s*x)*theta x)=0
  rw [hmel.2,mul_zero]

private theorem gaussian_eval (s : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (s*x)*pulse 0 x) ∧
    (∫ x : ℝ, Complex.exp (s*x)*pulse 0 x)=Complex.exp (s^2/4) := by
  let c : ℂ := ((1/Real.sqrt Real.pi:ℝ):ℂ)
  have hg (x : ℝ) : Complex.exp (s*x)*pulse 0 x =
      c*Complex.exp ((-1:ℂ)*(x:ℂ)^2+s*x+0) := by
    simp only [pulse,zero_add,one_mul,c,add_zero,neg_one_mul,Complex.exp_add]
    ring
  simp_rw [hg]
  refine ⟨(integrable_cexp_quadratic' (b:=(-1:ℂ)) (by norm_num) s 0).const_mul _,?_⟩
  rw [integral_const_mul,integral_cexp_quadratic (b:=(-1:ℂ)) (by norm_num)]
  have hr : (Real.pi:ℂ)^(1/2:ℂ)=(Real.sqrt Real.pi:ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow Real.pi_pos.le]
    norm_num
  have hπ : ((Real.sqrt Real.pi : ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
  simp only [neg_neg,div_one,hr,c,Complex.ofReal_div,Complex.ofReal_one]
  rw [←mul_assoc,one_div_mul_cancel hπ,one_mul]
  congr 1
  ring

/-- A zeta zero annihilates every translated theta term at its own complex
argument. The unit-width Gaussian leaves the same nonzero value at every height. -/
theorem solution {m : ℕ} (a : Fin m → ℂ) (y : Fin m → ℝ) (s : ℂ)
    (hs : 0<s.re) (hs' : s.re<1) (hz : riemannZeta s=0) :
    Integrable (fun x : ℝ => Complex.exp (s*x)*residual 0 a y x) ∧
    (∫ x : ℝ, Complex.exp (s*x)*residual 0 a y x)=Complex.exp (s^2/4) := by
  let f (i : Fin m) (x : ℝ) := Complex.exp (s*x)*theta (x-y i)
  have h (i : Fin m) := theta_eval s hs hs' hz (y i)
  have hi (i : Fin m) : Integrable (fun x => a i*f i x) := (h i).1.const_mul _
  have split (x : ℝ) : Complex.exp (s*x)*residual 0 a y x =
      Complex.exp (s*x)*pulse 0 x-∑ i, a i*f i x := by
    simp only [MasulloRH.GaussianApproximation.residual,mul_sub,Finset.mul_sum,f,mul_left_comm]
  simp_rw [split]
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  refine ⟨(gaussian_eval s).1.sub hsum,?_⟩
  rw [integral_sub (gaussian_eval s).1 hsum,integral_finsetSum _ (fun i _ => hi i),(gaussian_eval s).2]
  simp only [integral_const_mul,f,(h _).2,mul_zero,Finset.sum_const_zero,sub_zero]
