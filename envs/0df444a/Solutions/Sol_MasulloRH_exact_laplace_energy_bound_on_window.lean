-- Prove2me | solution 1 for MasulloRH.exact_laplace_energy_bound_on_window
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:23:44.253108+00:00
-- url     : https://prove2.me/submissions/e6b2bba3-7c43-4137-a315-3a422607ec3c

import Theorems.Thm_MasulloAudit_window_mellin_evaluation_bounded
import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- The exponential weight factorization follows the accepted rectangle proof. This estimate retains the exact two-sided evaluation constant.
https://prove2.me/submissions/5b2cbfbc-22d8-4073-bb0e-dbecd2699cb3 -/

open MeasureTheory Filter MasulloRH.GaussianApproximation

/-- Exact squared evaluation constant in the two-sided exponential window.
The error function enters only through its weighted squared norm. -/
theorem solution (f : ℝ → ℂ) (c b : ℝ) (s : ℂ) (hs : |s.re-c|<b)
    (hi : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖f x‖^2)) :
    ‖∫ x : ℝ, Complex.exp (s*x)*f x‖^2 ≤ energy c b f *
      (1/(2*(b-(s.re-c))) + 1/(2*(b+(s.re-c)))) := by
  let A (x : ℝ) := Real.exp (c*x+b*|x|)*‖f x‖
  let B (x : ℝ) := Real.exp ((s.re-c)*x-b*|x|)
  let C : ℝ := 1/(2*(b-(s.re-c)))+1/(2*(b+(s.re-c)))
  have apos (x : ℝ) : 0≤A x := mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
  have a2 (x : ℝ) : A x ^ 2=Real.exp (2*c*x+2*b*|x|)*‖f x‖^2 := by
    simp only [A,mul_pow,←Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have b2 (x : ℝ) : B x^2=Real.exp (2*(s.re-c)*x-2*b*|x|) := by
    dsimp only [B]
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have am : AEStronglyMeasurable A volume := by
    have eq : A = fun x => Real.sqrt (Real.exp (2*c*x+2*b*|x|)*‖f x‖^2) := by
      funext x
      rw [←a2,Real.sqrt_sq (apos x)]
    rw [eq]
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hi.1
  have la : MemLp A 2 volume := (memLp_two_iff_integrable_sq am).2 (by simpa only [a2] using hi)
  have re : (s-(c:ℂ)).re=s.re-c := by simp
  obtain ⟨bi,bint,_,_⟩ := MasulloAudit.window_mellin_evaluation_bounded b
    ((abs_nonneg _).trans_lt hs) (s-(c:ℝ)) (re ▸ hs)
  rw [re] at bi bint
  have lb : MemLp B 2 volume := (memLp_two_iff_integrable_sq (by dsimp [B];fun_prop)).2
    (by simpa only [b2] using bi)
  have joint (x : ℝ) : ‖Complex.exp (s*x)*f x‖=A x*B x := by
    simp only [B,A,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    rw [mul_right_comm,←Real.exp_add]
    congr 2
    ring
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ:=volume) (p:=2) (q:=2)
    (by norm_num [Real.holderConjugate_iff]) (f:=A) (g:=B) (ae_of_all _ apos)
    (ae_of_all _ fun x => Real.exp_nonneg _) (by simpa using la) (by simpa using lb)
  have hnorm : ‖∫ x : ℝ, Complex.exp (s*x)*f x‖ ≤ Real.sqrt (energy c b f)*Real.sqrt C := by
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [joint]
    simpa only [Real.rpow_two,a2,b2,bint,←Real.sqrt_eq_rpow,C,energy] using holder
  have hE : 0≤energy c b f := integral_nonneg (fun _ => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  have hC : 0≤C := by
    dsimp only [C]
    rw [←bint]
    exact integral_nonneg (fun _ => Real.exp_nonneg _)
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hnorm
  simpa only [mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hC,C] using hsquare
