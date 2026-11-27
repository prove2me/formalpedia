-- Prove2me | solution 1 for MasulloRH.real_residual_conjugate_frequency_gain
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:17:53.446287+00:00
-- url     : https://prove2.me/submissions/8db8ad70-e5a5-4376-a652-4c3f371dda16

import Theorems.Thm_MasulloRH_finite_laplace_evaluations_weighted_energy_bound
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory MasulloRH.WindowLaplaceGram MasulloRH.GaussianApproximation
open scoped ComplexConjugate

private noncomputable def diag (c b σ : ℝ) : ℝ := 1/(2*(σ-(c-b))) + 1/(2*((c+b)-σ))

private theorem same_freq (c b : ℝ) (s : ℂ) :
    kernel c b s s = ((diag c b s.re : ℝ) : ℂ) := by
  have hs := Complex.add_conj s
  rw [kernel,hs,diag]
  push_cast
  congr 2 <;> ring

private theorem separated (c b : ℝ) (s : ℂ) (ht : 0 < |s.im|) :
    ‖kernel c b s (conj s)‖ ≤ 1/|s.im| := by
  let l := s+s-((2*(c-b):ℝ):ℂ)
  let r := ((2*(c+b):ℝ):ℂ)-(s+s)
  have absL : |l.im|=2*|s.im| := by simp [l,←two_mul,abs_mul]
  have absR : |r.im|=2*|s.im| := by simp [r,←two_mul,abs_mul]
  have hn (v : ℂ) (hv : |v.im|=2*|s.im|) : ‖1/v‖ ≤ 1/(2*|s.im|) := by
    rw [norm_div,norm_one]
    exact one_div_le_one_div_of_le (by positivity) (hv ▸ Complex.abs_im_le_norm v)
  have bound := (norm_add_le (1/l) (1/r)).trans (add_le_add (hn l absL) (hn r absR))
  have cancel : (1:ℝ)/(2*|s.im|)+1/(2*|s.im|) = 1/|s.im| := by ring
  simpa only [kernel,starRingEnd_self_apply,l,r,cancel] using bound

theorem solution (c b : ℝ) (f : ℝ → ℂ) (s : ℂ) (hs : |s.re-c| < b) (ht : 0 < |s.im|)
    (hf : ∀ x, conj (f x) = f x)
    (hi : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖f x‖^2))
    (hm : Integrable (fun x : ℝ => Complex.exp (s*x)*f x)) :
    2 * ‖moment f s‖^2 ≤ energy c b f *
      (1/(2*(s.re-(c-b))) + 1/(2*((c+b)-s.re)) + 1/|s.im|) := by
  classical
  let z : Fin 2 → ℂ := ![s,conj s]
  let v := moment f s
  let d : Fin 2 → ℂ := ![conj v,v]
  have hc (x : ℝ) : Complex.exp (conj s*x)*f x = conj (Complex.exp (s*x)*f x) := by
    rw [map_mul,← Complex.exp_conj,map_mul,Complex.conj_ofReal,hf]
  have hcI : Integrable (fun x : ℝ => Complex.exp (conj s*x)*f x) := by
    simp_rw [hc]
    exact (RCLike.conjLIE.integrable_comp_iff).2 hm
  have hcM : moment f (conj s) = conj v := by
    dsimp only [moment,v];simp_rw [hc];exact integral_conj
  have hh := (MasulloRH.finite_laplace_evaluations_weighted_energy_bound c b f z d
    (fun i => by fin_cases i <;> simpa [z] using hs) hi
    (fun i => by fin_cases i;exact hm;exact hcI)).2
  have hE : 0 ≤ energy c b f := integral_nonneg (fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have vcon : v*conj v = ((‖v‖^2:ℝ):ℂ) := by rw [Complex.mul_conj,Complex.sq_norm]
  have conv : conj v*v = ((‖v‖^2:ℝ):ℂ) := by rw [mul_comm,vcon]
  have total : ‖∑ i, d i * moment f (z i)‖ = 2*‖v‖^2 := by
    simp only [Fin.sum_univ_two,z,d,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,hcM]
    change ‖conj v*v+v*conj v‖=_
    rw [vcon,conv,←Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by positivity)];ring
  have term (a w k : ℂ) (ha : ‖a‖=‖v‖) (hw : ‖w‖=‖v‖) (hk : ‖k‖≤1/|s.im|) :
      (a*w*k).re ≤ ‖v‖^2*(1/|s.im|) := by
    apply (Complex.re_le_norm _).trans
    rw [norm_mul,norm_mul,ha,hw,pow_two]
    exact mul_le_mul_of_nonneg_left hk (by positivity)
  have h₁ := term (conj v) (conj v) (kernel c b s (conj s)) (Complex.norm_conj _) (Complex.norm_conj _) (separated c b s ht)
  have rev : ‖kernel c b (conj s) s‖ ≤ 1/|s.im| := by
    simpa using separated c b (conj s) (by simpa using ht)
  have h₂ := term v v (kernel c b (conj s) s) rfl rfl rev
  have gbound : gramValue c b z d ≤ 2*‖v‖^2*(diag c b s.re+1/|s.im|) := by
    simp only [gramValue,Fin.sum_univ_two,z,d,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,starRingEnd_self_apply,vcon,conv,same_freq,
      Complex.conj_re,←Complex.ofReal_mul,Complex.add_re,Complex.ofReal_re]
    linarith only [h₁,h₂]
  rw [total] at hh
  have hp := hh.trans (mul_le_mul_of_nonneg_left gbound hE)
  by_cases zv : ‖v‖^2=0
  · have hD : 0 ≤ diag c b s.re := by
      dsimp only [diag]
      have hl : 0 < s.re-(c-b) := by linarith [(abs_lt.mp hs).1]
      have hr : 0 < (c+b)-s.re := by linarith [(abs_lt.mp hs).2]
      positivity
    change 2*‖v‖^2 ≤ energy c b f * (diag c b s.re + 1/|s.im|)
    rw [zv,mul_zero]
    exact mul_nonneg hE (add_nonneg hD (by positivity))
  · have pos : 0 < 2*‖v‖^2 := mul_pos (by norm_num) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm zv))
    change 2*‖v‖^2 ≤ energy c b f * (diag c b s.re + 1/|s.im|)
    apply le_of_mul_le_mul_left _ pos
    linarith only [hp]
