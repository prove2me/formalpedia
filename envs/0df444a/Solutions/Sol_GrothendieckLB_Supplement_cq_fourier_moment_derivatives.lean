-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_fourier_moment_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:43:39.801803+00:00
-- url     : https://prove2.me/submissions/97192c04-7709-4539-8704-ce25efa2882d

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

private noncomputable def env (R : ℝ) (m n : ℕ) (w : ℝ×ℝ) :=
  (|w.1|^m*exp (-((1-R)/2)*w.1^2))*(|w.2|^n*exp (-((1-R)/2)*w.2^2))

private theorem env_int {R : ℝ} (hR : R<1) (m n : ℕ) : Integrable (env R m n) := by
  have hb : 0<(1-R)/2 := by linarith
  exact (raw_integrable _ hb m).mul_prod (raw_integrable _ hb n)

private theorem kernel_le {R t : ℝ} (ht : |t|≤R) (x y : ℝ) :
    -(x^2+y^2+2*t*x*y)/2 ≤ -((1-R)/2)*x^2 + -((1-R)/2)*y^2 := by
  have hn : 0≤R := (abs_nonneg _).trans ht
  obtain ⟨hl,hh⟩ := abs_le.mp ht
  by_cases h : 0≤x*y
  · nlinarith only [mul_le_mul_of_nonneg_right hl h,mul_nonneg hn (sq_nonneg (x-y))]
  · nlinarith only [mul_le_mul_of_nonpos_right hh (le_of_not_ge h),mul_nonneg hn (sq_nonneg (x+y))]

private theorem norm_osc (q : ℂ) (u v : ℝ) (m n : ℕ) (w : ℝ×ℝ) :
    ‖osc q u v m n w‖ = |w.1|^m*|w.2|^n*exp (-(w.1^2+w.2^2+2*q.re*w.1*w.2)/2) := by
  simp only [osc,norm_mul,norm_pow,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
  congr 2
  unfold phase
  rw [div_eq_mul_inv]
  simp [Complex.add_re,Complex.neg_re,Complex.mul_re,Complex.mul_im,pow_two]
  <;> ring

private theorem osc_le (q : ℂ) (u v : ℝ) (m n : ℕ) (w : ℝ×ℝ) (R : ℝ) (h : |q.re|≤R) :
    ‖osc q u v m n w‖ ≤ env R m n w := by
  rw [norm_osc]
  calc
    _ ≤ |w.1|^m*|w.2|^n*(exp (-((1-R)/2)*w.1^2)*exp (-((1-R)/2)*w.2^2)) := by
      rw [← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (kernel_le h _ _)) (by positivity)
    _ = _ := by unfold env;ring

private theorem cont (q u v : ℂ) (m n : ℕ) : Continuous (osc q u v m n) := by unfold osc phase;fun_prop
private theorem osc_int (q : ℂ) (hq : |q.re|<1) (u v : ℝ) (m n : ℕ) :
    Integrable (osc q u v m n) :=
  (env_int hq m n).mono' (cont _ _ _ _ _).aestronglyMeasurable (Eventually.of_forall fun w => osc_le _ _ _ _ _ w _ le_rfl)

private theorem affine_at (f : ℂ→ℂ) (z A B : ℂ) (he : ∀ w : ℂ, f w=A+B*w) :
    HasDerivAt f B z := by
  have h : HasDerivAt (fun w : ℂ => A+B*w) B z := by
    simpa only [id_eq,mul_one] using! (((hasDerivAt_id z).const_mul B).const_add A)
  exact h.congr_of_eventuallyEq (Eventually.of_forall he)

private theorem cov_at (q u v : ℂ) (m n : ℕ) (w : ℝ×ℝ) :
    HasDerivAt (fun r => osc r u v m n w) (osc q u v (m+1) (n+1) w) q := by
  let B := -((w.1:ℂ)*w.2)
  have h := affine_at (fun r => phase r u v w) q (phase 0 u v w) B (fun r => by unfold phase B;ring)
  have e : ((Complex.I*(w.1:ℂ))^m*(Complex.I*(w.2:ℂ))^n)*(Complex.exp (phase q u v w)*B)=osc q u v (m+1) (n+1) w := by
    unfold osc B
    rw [pow_succ,pow_succ]
    linear_combination (norm := ring) (-((Complex.I*(w.1:ℂ))^m*(Complex.I*(w.2:ℂ))^n*(w.1:ℂ)*(w.2:ℂ)*Complex.exp (phase q u v w))) * Complex.I_sq
  rw [← e]
  exact h.cexp.const_mul _

private theorem shift₁_at (q : ℂ) (u v : ℝ) (m n : ℕ) (w : ℝ×ℝ) :
    HasDerivAt (fun s : ℝ => osc q s v m n w) (osc q u v (m+1) n w) u := by
  let B := Complex.I*(w.1:ℂ)
  have h := affine_at (fun s => phase q s v w) u (phase q 0 v w) B (fun s => by unfold phase B;ring)
  have e : ((Complex.I*(w.1:ℂ))^m*(Complex.I*(w.2:ℂ))^n)*(Complex.exp (phase q u v w)*B)=osc q u v (m+1) n w := by
    unfold osc B
    rw [pow_succ]
    ring
  rw [← e]
  exact (h.cexp.const_mul _).comp_ofReal

private theorem shift₂_at (q : ℂ) (u v : ℝ) (m n : ℕ) (w : ℝ×ℝ) :
    HasDerivAt (fun s : ℝ => osc q u s m n w) (osc q u v m (n+1) w) v := by
  let B := Complex.I*(w.2:ℂ)
  have h := affine_at (fun s => phase q u s w) v (phase q u 0 w) B (fun s => by unfold phase B;ring)
  have e : ((Complex.I*(w.1:ℂ))^m*(Complex.I*(w.2:ℂ))^n)*(Complex.exp (phase q u v w)*B)=osc q u v m (n+1) w := by
    unfold osc B
    rw [pow_succ]
    ring
  rw [← e]
  exact (h.cexp.const_mul _).comp_ofReal

private theorem dominated {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 ℂ]
    (f g : 𝕜 → ℝ×ℝ → ℂ) (s : Set 𝕜) (x : 𝕜) (hs : s∈𝓝 x) (M : ℝ×ℝ → ℝ)
    (hm : Integrable M) (hf : Integrable (f x))
    (cf : ∀ w,Continuous (f w)) (cg : Continuous (g x))
    (hg : ∀ r∈s,∀ y, ‖g r y‖≤M y)
    (hd : ∀ r∈s,∀ y,HasDerivAt (fun v => f v y) (g r y) r) :
    HasDerivAt (fun v => ∫ y : ℝ×ℝ,f v y) (∫ y : ℝ×ℝ,g x y) x :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=volume) (F:=f) (F':=g) hs
    (Eventually.of_forall fun w => (cf w).aestronglyMeasurable) hf cg.aestronglyMeasurable
    (Eventually.of_forall fun y r hr => hg r hr y) hm (Eventually.of_forall fun y r hr => hd r hr y)).2

end CQFourierDerivative

open CQFourierDerivative
theorem solution (q : ℂ) (hq : |q.re|<1) (u v : ℝ) (m n : ℕ) :
    HasDerivAt (fun r : ℂ => fourierMoment r u v m n) (fourierMoment q u v (m+1) (n+1)) q ∧
    HasDerivAt (fun s : ℝ => fourierMoment q s v m n) (fourierMoment q u v (m+1) n) u ∧
    HasDerivAt (fun s : ℝ => fourierMoment q u s m n) (fourierMoment q u v m (n+1)) v ∧
    Continuous (fun w : ℝ×ℝ => fourierMoment q w.1 w.2 m n) := by
  let R := (|q.re|+1)/2
  have hR : R<1 := by dsimp [R];linarith
  have hin : |q.re|<R := by dsimp [R];linarith
  have hs : {r : ℂ | |r.re|<R}∈𝓝 q := (isOpen_lt Complex.continuous_re.abs continuous_const).mem_nhds hin
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)
  refine ⟨?_,?_,?_,?_⟩
  · have h := dominated (fun r : ℂ => osc r u v m n) (fun r : ℂ => osc r u v (m+1) (n+1))
      _ q hs (env R (m+1) (n+1)) (env_int hR _ _) (osc_int q hq _ _ _ _)
      (fun r => cont _ _ _ _ _) (cont _ _ _ _ _)
      (fun r hr w => osc_le _ _ _ _ _ w _ (le_of_lt hr))
      (fun r _ w => cov_at r u v m n w)
    exact h.const_mul c
  · have h := dominated (fun s : ℝ => osc q s v m n) (fun s : ℝ => osc q s v (m+1) n)
      Set.univ u Filter.univ_mem (env |q.re| (m+1) n) (env_int hq _ _) (osc_int q hq _ _ _ _)
      (fun s => cont _ _ _ _ _) (cont _ _ _ _ _)
      (fun s _ w => osc_le _ _ _ _ _ w _ le_rfl) (fun s _ w => shift₁_at q s v m n w)
    exact h.const_mul c
  · have h := dominated (fun s : ℝ => osc q u s m n) (fun s : ℝ => osc q u s m (n+1))
      Set.univ v Filter.univ_mem (env |q.re| m (n+1)) (env_int hq _ _) (osc_int q hq _ _ _ _)
      (fun s => cont _ _ _ _ _) (cont _ _ _ _ _)
      (fun s _ w => osc_le _ _ _ _ _ w _ le_rfl) (fun s _ w => shift₂_at q u s m n w)
    exact h.const_mul c
  · have h := continuous_of_dominated (μ:=volume) (F:=fun (w : ℝ×ℝ) y => osc q w.1 w.2 m n y)
        (fun _ => (cont _ _ _ _ _).aestronglyMeasurable)
        (fun w => Eventually.of_forall fun y => osc_le q w.1 w.2 m n y _ le_rfl)
        (env_int hq m n) (Eventually.of_forall fun y => by unfold osc phase;fun_prop)
    exact continuous_const.mul h