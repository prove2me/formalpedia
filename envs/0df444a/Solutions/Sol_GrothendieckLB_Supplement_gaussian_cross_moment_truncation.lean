-- Prove2me | solution 1 for GrothendieckLB.Supplement.gaussian_cross_moment_truncation
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:51:27.598501+00:00
-- url     : https://prove2.me/submissions/d1e72093-bd78-4bd3-b867-e59bba65146e

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

private theorem exponential_tail (x q : ℝ) (hq : 1 ≤ q) (l : ℕ) :
    |Real.exp x - ∑ j ∈ Finset.range l, x^j/j.factorial| ≤ Real.exp (q*|x|)/q^l := by
  let f (t : ℝ) (n : ℕ) : ℝ := t^n/n.factorial
  have hs (t : ℝ) : HasSum (f t) (Real.exp t) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp t
  have hq0 : 0 < q := by linarith
  have shift (t : ℝ) : Summable (fun n => f t (n+l)) :=
    (summable_nat_add_iff l).mpr (hs t).summable
  have splitSum (t : ℝ) : (∑ j ∈ Finset.range l, f t j)+(∑' n, f t (n+l))=Real.exp t :=
    ((hs t).summable.sum_add_tsum_nat_add l).trans (hs t).tsum_eq
  have ev : Real.exp x - (∑ j ∈ Finset.range l, f x j)=∑' n, f x (n+l) := by linarith only [splitSum x]
  change |Real.exp x - ∑ j ∈ Finset.range l, f x j| ≤ _
  rw [ev]
  have habs (n : ℕ) : ‖f x n‖=f |x| n := by
    simp [f,Real.norm_eq_abs]
  have hn := norm_tsum_le_tsum_norm ((shift |x|).congr fun n => (habs (n+l)).symm)
  simp only [Real.norm_eq_abs] at hn
  have A : |∑' n, f x (n+l)| ≤ ∑' n, f |x| (n+l) := by
    simpa only [←Real.norm_eq_abs,habs] using hn
  have B (n : ℕ) : f |x| (n+l) ≤ f (q*|x|) (n+l)/q^l := by
    apply (le_div_iff₀ (pow_pos hq0 _)).mpr
    have ht : 0 ≤ f |x| (n+l) := by unfold f; positivity
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq (show l≤n+l by omega)) ht
    refine h.trans_eq ?_
    simp only [f,mul_pow]
    ring
  have C := (shift |x|).tsum_le_tsum B ((shift (q*|x|)).div_const (q^l))
  rw [tsum_div_const] at C
  refine A.trans (C.trans (div_le_div_of_nonneg_right ?_ (pow_nonneg hq0.le _)))
  have t : 0 ≤ ∑ j ∈ Finset.range l, f (q*|x|) j := by
    apply Finset.sum_nonneg;intro j _;dsimp [f];positivity
  linarith only [splitSum (q*|x|),t]

private theorem kernelTail (A B u v q : ℝ) (hq : 1 ≤ q) (K : ℕ) :
    |Real.exp (-(A*(u^2+v^2))+2*B*u*v) -
      Real.exp (-(A*(u^2+v^2))) * (∑ k ∈ Finset.range (K+1), (2*B*u*v)^k/k.factorial)| ≤
      Real.exp (-(A-q*|B|)*(u^2+v^2))/q^(K+1) := by
  let z := 2*B*u*v
  let s := u^2+v^2
  have hq0 : 0 ≤ q := by linarith
  have hm : |z|≤|B| * s := by
    have h : 2*|u| * |v| ≤ s := by dsimp [s];nlinarith only [sq_nonneg (|u|-|v|),sq_abs u,sq_abs v]
    dsimp [z];rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    nlinarith only [mul_le_mul_of_nonneg_left h (abs_nonneg B)]
  change |Real.exp (-(A*s)+z)-Real.exp (-(A*s))*(∑ k ∈ Finset.range (K+1), z^k/k.factorial)| ≤ _
  rw [Real.exp_add,←mul_sub,abs_mul,abs_of_pos (Real.exp_pos _)]
  refine (mul_le_mul_of_nonneg_left (exponential_tail z q hq (K+1)) (Real.exp_pos _).le).trans ?_
  rw [←mul_div_assoc,←Real.exp_add]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hq0 _)
  apply Real.exp_le_exp.mpr
  change -(A*s)+q*|z| ≤ -(A-q*|B|)*s
  nlinarith only [mul_le_mul_of_nonneg_left hm hq0]

open MeasureTheory ProbabilityTheory

theorem solution (A B q : ℝ) (hq : 1 ≤ q) (K : ℕ) (U F G : ℝ → ℝ) :
    let μ := gaussianReal 0 1
    let w (a : ℝ) (k : ℕ) (P : ℝ → ℝ) (x : ℝ) := P x*(U x)^k*Real.exp (-a*(U x)^2)
    let f (z : ℝ×ℝ) := F z.1*G z.2*Real.exp (-(A*((U z.1)^2+(U z.2)^2))+2*B*U z.1*U z.2)
    let decay := A-q*|B|
    Integrable f (μ.prod μ) →
    (∀ k ≤ K, Integrable (w A k F) μ ∧ Integrable (w A k G) μ) →
    Integrable (w decay 0 (fun x => |F x|)) μ →
    Integrable (w decay 0 (fun x => |G x|)) μ →
    |(∫ z, f z ∂μ.prod μ) - ∑ k ∈ Finset.range (K+1), ((2*B)^k/k.factorial) *
       ((∫ x, w A k F x ∂μ)*(∫ y, w A k G y ∂μ))| ≤
       ((∫ x, w decay 0 (fun s => |F s|) x ∂μ)*(∫ y, w decay 0 (fun s => |G s|) y ∂μ))/q^(K+1) := by
  intro μ w f lam hf hw hF hG
  let c (k : ℕ) := (2*B)^k/k.factorial
  let term (k : ℕ) (t : ℝ×ℝ) := c k*(w A k F t.1*w A k G t.2)
  let fs (t : ℝ×ℝ) := ∑ k ∈ Finset.range (K+1), term k t
  let tail (t : ℝ×ℝ) := (w lam 0 (fun s => |F s|) t.1*w lam 0 (fun s => |G s|) t.2)/q^(K+1)
  have ti (k : ℕ) (hk : k∈Finset.range (K+1)) : Integrable (term k) (μ.prod μ) := by
    obtain ⟨v₁,v₂⟩ := hw k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    exact (v₁.mul_prod v₂).const_mul (c k)
  have si : Integrable fs (μ.prod μ) := integrable_finsetSum _ ti
  have ui : Integrable tail (μ.prod μ) := (hF.mul_prod hG).div_const _
  have se : (∫ t, fs t ∂μ.prod μ)=∑ k ∈ Finset.range (K+1),
      c k*((∫ x, w A k F x ∂μ)*(∫ y, w A k G y ∂μ)) := by
    rw [show (∫ t, fs t ∂μ.prod μ)=_ from integral_finsetSum _ ti]
    apply Finset.sum_congr rfl
    intro k _
    rw [show (∫ t, term k t ∂μ.prod μ)=_ from integral_const_mul _ _,integral_prod_mul]
  have te : (∫ t, tail t ∂μ.prod μ)=
      ((∫ x, w lam 0 (fun s => |F s|) x ∂μ)*(∫ y, w lam 0 (fun s => |G s|) y ∂μ))/q^(K+1) := by
    rw [show (∫ t, tail t ∂μ.prod μ)=_ from integral_div _ _,integral_prod_mul]
  have sep (a u v : ℝ) : Real.exp (-(a*(u^2+v^2)))=Real.exp (-a*u^2)*Real.exp (-a*v^2) := by
    rw [← Real.exp_add];congr 1;ring
  have per (t : ℝ×ℝ) : |f t-fs t| ≤ tail t := by
    let u := U t.1
    let v := U t.2
    have he : fs t=F t.1*G t.2*(Real.exp (-(A*(u^2+v^2)))*
        ∑ k ∈ Finset.range (K+1), (2*B*u*v)^k/k.factorial) := by
      rw [sep,Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [term,c,w,u,v]
      simp only [mul_pow]
      ring
    rw [he]
    change |F t.1*G t.2*Real.exp (-(A*(u^2+v^2))+2*B*u*v)-
      F t.1*G t.2*_| ≤_
    rw [←mul_sub,abs_mul]
    refine (mul_le_mul_of_nonneg_left (kernelTail A B u v q hq K) (abs_nonneg _)).trans_eq ?_
    change |F t.1*G t.2| * (Real.exp (-(lam)*(u^2+v^2))/q^(K+1))=_
    rw [show -(lam)*(u^2+v^2)= -(lam*(u^2+v^2)) by ring,sep,abs_mul]
    dsimp only [tail,w,pow_zero,mul_one,u,v]
    ring
  change |(∫ t, f t ∂μ.prod μ)-(∑ k ∈ Finset.range (K+1), c k*_)| ≤_
  rw [←se,←te,←integral_sub hf si]
  exact abs_integral_le_integral_abs.trans
    (integral_mono (hf.sub si).abs ui per)
