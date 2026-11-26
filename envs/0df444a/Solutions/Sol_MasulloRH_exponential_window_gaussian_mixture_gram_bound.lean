-- Prove2me | solution 1 for MasulloRH.exponential_window_gaussian_mixture_gram_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:17:10.64906+00:00
-- url     : https://prove2.me/submissions/f3791aef-1024-4434-9c8e-4ee985289c14

import Definitions.Def_MasulloRH_GaussianMixtureWindows
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Real MasulloRH.GaussianMixture MasulloRH.GaussianApproximation

private theorem weight_bound (c b x : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) :
    exp (2*c*x + 2*b*|x|) ≤ exp (2*x) + 1/4 := by
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    exact (exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hr) hx])).trans
      (le_add_of_nonneg_right (by norm_num))
  · rw [abs_of_nonpos hx]
    have le : 2*c*x+2*b*(-x) ≤ x := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) hx]
    apply (exp_le_exp.mpr le).trans
    rw [two_mul,exp_add];nlinarith [sq_nonneg (exp x-1/2)]

private theorem overlap (p q y z t : ℝ) (hp : 0<p) (hq : 0<q) :
    Integrable (fun x : ℝ => exp (t*x)*(bell p y x*bell q z x)) ∧
    (∫ x : ℝ, exp (t*x)*(bell p y x*bell q z x))=kernel p q y z t := by
  let d := p^2+q^2
  let u := (2*p^2*y+2*q^2*z+t)/(2*d)
  let g := fun x : ℝ => exp (-d*x^2)
  have hd : 0<d := by dsimp [d];positivity
  have gi : Integrable g := integrable_exp_neg_mul_sq hd
  have sc : (p/sqrt π)*(q/sqrt π)=p*q/π := by
    rw [div_mul_div_comm,Real.mul_self_sqrt pi_pos.le]
  have id : (fun x : ℝ => exp (t*x)*(bell p y x*bell q z x)) =
      fun x => (p*q/π*exp (exponent p q y z t))*g (x-u) := by
    funext x
    have ex : exp (t*x)*exp (-(p^2)*(x-y)^2)*exp (-(q^2)*(x-z)^2)=
        exp (exponent p q y z t)*g (x-u) := by
      dsimp only [g];rw [←exp_add,←exp_add,←exp_add];congr 1
      dsimp [exponent,u,d]
      have hn : p^2+q^2≠0 := hd.ne'
      field_simp [hn];ring
    calc
      _ = ((p/sqrt π)*(q/sqrt π))*(exp (t*x)*exp (-(p^2)*(x-y)^2)*exp (-(q^2)*(x-z)^2)) := by unfold bell;ring
      _ = _ := by rw [sc,ex];ring
  rw [id]
  refine ⟨(gi.comp_sub_right _).const_mul _,?_⟩
  rw [integral_const_mul,integral_sub_right_eq_self,show (∫ x : ℝ, g x)=sqrt (π/d) from integral_gaussian d]
  dsimp [kernel,ratio,d];ring

/-- The weighted energy of any real signed finite sum of normalized shifted Gaussians is bounded by an explicit overlap matrix. -/
theorem solution {m : ℕ} (a p y : Fin m → ℝ) (hp : ∀ i, 0<p i) (c b : ℝ)
    (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) :
    let f := fun x : ℝ => ((∑ i, a i*bell (p i) (y i) x : ℝ) : ℂ)
    Integrable (fun x : ℝ => exp (2*c*x+2*b*|x|)*‖f x‖^2) ∧
    energy c b f ≤ ∑ i, ∑ j, a i*a j*(kernel (p i) (p j) (y i) (y j) 2 +
      (1/4)*kernel (p i) (p j) (y i) (y j) 0) := by
  let g := fun x : ℝ => ∑ i, a i*bell (p i) (y i) x
  let A := fun (i j : Fin m) (x : ℝ) => a i*a j*((exp (2*x)+1/4)*(bell (p i) (y i) x*bell (p j) (y j) x))
  let F := fun x : ℝ => ∑ i, ∑ j, A i j x
  have pair (i j : Fin m) : Integrable (A i j) ∧ (∫ x : ℝ, A i j x)=
      a i*a j*(kernel (p i) (p j) (y i) (y j) 2+(1/4)*kernel (p i) (p j) (y i) (y j) 0) := by
    let B := fun t (x : ℝ) => exp (t*x)*(bell (p i) (y i) x*bell (p j) (y j) x)
    have h (t : ℝ) := overlap (p i) (p j) (y i) (y j) t (hp i) (hp j)
    have i2 : Integrable (B 2) := (h 2).1
    have i0 : Integrable (fun x => (1/4)*B 0 x) := (h 0).1.const_mul _
    have eq : A i j = fun x => (a i*a j)*(B 2 x+(1/4)*B 0 x) := by
      funext x;dsimp [A,B];rw [zero_mul,exp_zero,one_mul];ring
    rw [eq]
    refine ⟨(i2.add i0).const_mul _,?_⟩
    rw [integral_const_mul,integral_add i2 i0,integral_const_mul]
    change a i*a j*((∫ x : ℝ, exp (2*x)*(bell (p i) (y i) x*bell (p j) (y j) x))+
      (1/4)*(∫ x : ℝ, exp (0*x)*(bell (p i) (y i) x*bell (p j) (y j) x)))=_
    rw [(h 2).2,(h 0).2]
  have row (i : Fin m) : Integrable (fun x => ∑ j, A i j x) :=
    integrable_finsetSum _ (fun j _ => (pair i j).1)
  have Fi : Integrable F := integrable_finsetSum _ (fun i _ => row i)
  have dom (x : ℝ) : exp (2*c*x+2*b*|x|)*‖(g x : ℂ)‖^2 ≤ F x := by
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
    apply (mul_le_mul_of_nonneg_right (weight_bound c b x hl hr) (sq_nonneg _)).trans
    apply le_of_eq
    dsimp [g,F,A];simp only [sq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro i hi;apply Finset.sum_congr rfl;intro j hj;ring
  have I : Integrable (fun x : ℝ => exp (2*c*x+2*b*|x|)*‖(g x : ℂ)‖^2) := by
    apply Fi.mono' (by dsimp [g,bell];fun_prop)
    apply ae_of_all;intro x;rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (exp_nonneg _) (sq_nonneg _))];exact dom x
  refine ⟨I,(integral_mono I Fi dom).trans_eq ?_⟩
  dsimp only [F];rw [integral_finsetSum _ (fun i _ => row i)]
  apply Finset.sum_congr rfl;intro i hi;rw [integral_finsetSum _ (fun j _ => (pair i j).1)]
  exact Finset.sum_congr rfl (fun j _ => (pair i j).2)
