-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_boundary_energy_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:06:08.715805+00:00
-- url     : https://prove2.me/submissions/c1083192-1610-4ce5-8b90-10ad8b22cca1

import Mathlib.Analysis.Calculus.Deriv.Shift
import Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel
import Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_kernel_bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib

open GrothendieckLB.Supplement CQBoundary Complex Set
open scoped Topology
set_option maxHeartbeats 1400000
noncomputable section
namespace KernelRegular

private def denom (z : ℂ) := 1 - rho z ^ 2
private def U := {z : ℂ | denom z ∈ slitPlane}
private theorem analyticRho (z : ℂ) : AnalyticAt ℂ rho z := by unfold rho; fun_prop
private theorem analyticDen (z : ℂ) : AnalyticAt ℂ denom z := by
  exact analyticAt_const.sub ((analyticRho z).pow _)
private theorem openU : IsOpen U := isOpen_slitPlane.preimage
  (continuous_iff_continuousAt.mpr fun z => (analyticDen z).continuousAt)

private inductive Poly where
  | coef (f : ℂ → ℂ) (hf : ∀ z ∈ U, AnalyticAt ℂ f z)
  | X | Y
  | add (p q : Poly) | mul (p q : Poly)

namespace Poly
private def con (a : ℂ) : Poly := .coef (fun _ => a) (fun _ _ => analyticAt_const)
private def ev : Poly → ℂ → ℝ → ℝ → ℂ
  | .coef f _, z, _, _ => f z
  | .X, _, x, _ => x
  | .Y, _, _, y => y
  | .add p q, z, x, y => ev p z x y + ev q z x y
  | .mul p q, z, x, y => ev p z x y * ev q z x y

private def dx : Poly → Poly
  | .coef .. => con 0
  | .X => con 1
  | .Y => con 0
  | .add p q => .add (dx p) (dx q)
  | .mul p q => .add (.mul (dx p) q) (.mul p (dx q))
private def dy : Poly → Poly
  | .coef .. => con 0
  | .X => con 0
  | .Y => con 1
  | .add p q => .add (dy p) (dy q)
  | .mul p q => .add (.mul (dy p) q) (.mul p (dy q))
private def dz : Poly → Poly
  | .coef f hf => .coef (deriv f) (fun z hz => (hf z hz).deriv)
  | .X => con 0
  | .Y => con 0
  | .add p q => .add (dz p) (dz q)
  | .mul p q => .add (.mul (dz p) q) (.mul p (dz q))

private theorem hdX (p : Poly) (z : ℂ) (x y : ℝ) :
    HasDerivAt (fun u : ℝ => p.ev z u y) (p.dx.ev z x y) x := by
  induction p with
  | coef f h => exact hasDerivAt_const _ _
  | X => simpa only [ev,dx,con,Complex.ofReal_one,id_eq] using! (hasDerivAt_id x).ofReal_comp
  | Y => exact hasDerivAt_const _ _
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq
private theorem hdY (p : Poly) (z : ℂ) (x y : ℝ) :
    HasDerivAt (fun v : ℝ => p.ev z x v) (p.dy.ev z x y) y := by
  induction p with
  | coef f h => exact hasDerivAt_const _ _
  | X => exact hasDerivAt_const _ _
  | Y => simpa only [ev,dy,con,Complex.ofReal_one,id_eq] using! (hasDerivAt_id y).ofReal_comp
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq
private theorem hdZ (p : Poly) {z : ℂ} (hz : z ∈ U) (x y : ℝ) :
    HasDerivAt (fun w : ℂ => p.ev w x y) (p.dz.ev z x y) z := by
  induction p with
  | coef f h => exact (h z hz).differentiableAt.hasDerivAt
  | X => exact hasDerivAt_const _ _
  | Y => exact hasDerivAt_const _ _
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq
private theorem cont (p : Poly) (z : ℂ) : Continuous (fun v : ℝ×ℝ => p.ev z v.1 v.2) := by
  induction p with
  | coef f h => exact continuous_const
  | X => exact continuous_ofReal.comp continuous_fst
  | Y => exact continuous_ofReal.comp continuous_snd
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

private def weight (x y : ℝ) := (1 + x^2) * (1 + y^2)
private theorem one_weight (x y : ℝ) : 1 ≤ weight x y := by
  unfold weight; nlinarith only [sq_nonneg x,sq_nonneg y,mul_nonneg (sq_nonneg x) (sq_nonneg y)]
private theorem growth (p : Poly) (z : ℂ) : ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧
    ∀ x y : ℝ, ‖p.ev z x y‖ ≤ C*(weight x y)^k := by
  induction p with
  | coef f h => exact ⟨‖f z‖,0,norm_nonneg _,by simp [ev]⟩
  | X =>
    refine ⟨1,1,zero_le_one,?_⟩
    intro x y
    simp only [ev,norm_real,Real.norm_eq_abs,pow_one,one_mul,weight]
    nlinarith only [sq_nonneg (|x|-1),sq_abs x,sq_nonneg y,mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  | Y =>
    refine ⟨1,1,zero_le_one,?_⟩
    intro x y
    simp only [ev,norm_real,Real.norm_eq_abs,pow_one,one_mul,weight]
    nlinarith only [sq_nonneg (|y|-1),sq_abs y,sq_nonneg x,mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  | add p q hp hq =>
    obtain ⟨A,i,hA,ha⟩ := hp
    obtain ⟨B,j,hB,hb⟩ := hq
    refine ⟨A+B,i+j,add_nonneg hA hB,?_⟩
    intro x y
    apply (norm_add_le _ _).trans
    rw [add_mul]
    exact add_le_add ((ha x y).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (one_weight x y) (by omega : i ≤ i+j)) hA))
      ((hb x y).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (one_weight x y) (by omega : j ≤ i+j)) hB))
  | mul p q hp hq =>
    obtain ⟨A,i,hA,ha⟩ := hp
    obtain ⟨B,j,hB,hb⟩ := hq
    refine ⟨A*B,i+j,mul_nonneg hA hB,?_⟩
    intro x y
    simp only [ev,norm_mul,pow_add]
    have hx := (zero_le_one.trans (one_weight x y))
    calc _ ≤ (A*weight x y^i)*(B*weight x y^j) := mul_le_mul (ha x y) (hb x y) (norm_nonneg _) (mul_nonneg hA (pow_nonneg hx _))
         _ = _ := by ring
end Poly
open Poly

private def negP (p : Poly) : Poly := .mul (.con (-1)) p
private def subP (p q : Poly) : Poly := .add p (negP q)
private def powP (p : Poly) : ℕ → Poly
  | 0 => .con 1
  | n+1 => .mul (powP p n) p
private theorem ev_powP (p : Poly) (n : ℕ) (z : ℂ) (x y : ℝ) :
    (powP p n).ev z x y = (p.ev z x y)^n := by
  induction n with
  | zero => simp [powP,ev,con]
  | succ n ih => simp [powP,ev,ih,pow_succ]
private def T (p : Poly) : Poly := .mul (.con (slope:ℂ)) (subP (powP p 3) (.mul (.con 3) p))
private def Tp (p : Poly) : Poly := .mul (.con (slope:ℂ)) (subP (.mul (.con 3) (powP p 2)) (.con 3))
private def Z : Poly := .coef id (fun _ _ => analyticAt_id)
private def R : Poly := .coef rho (fun z _ => analyticRho z)
private def E : Poly := .coef rhoEuler (by intro z _; unfold rhoEuler; fun_prop)
private def D : Poly := .coef (fun z => (denom z)⁻¹)
  (fun z hz => (analyticDen z).inv (slitPlane_ne_zero hz))
private def S : Poly := .coef (fun z => ((denom z) ^ (1/2:ℂ))⁻¹)
  (fun z hz => ((analyticDen z).cpow analyticAt_const hz).inv
    ((cpow_ne_zero_iff.mpr (.inl (slitPlane_ne_zero hz)))))
private def q : Poly :=
  .mul (.con (-(1/2 : ℂ))) (.mul D (.add (subP (powP (T .X) 2)
    (.mul (.con 2) (.mul R (.mul (T .X) (T .Y))))) (powP (T .Y) 2)))
private def pOne : Poly := .mul (subP E (.mul Z (.mul (Tp .X) (Tp .Y)))) S

private theorem evT_x (z : ℂ) (x y : ℝ) : (T .X).ev z x y = threshold x := by
  simp only [T,subP,negP,ev,con,ev_powP,threshold]; push_cast; ring
private theorem evT_y (z : ℂ) (x y : ℝ) : (T .Y).ev z x y = threshold y := by
  simp only [T,subP,negP,ev,con,ev_powP,threshold]; push_cast; ring
private theorem evTp_x (z : ℂ) (x y : ℝ) : (Tp .X).ev z x y = thresholdDeriv x := by
  simp only [Tp,subP,negP,ev,con,ev_powP,thresholdDeriv]; push_cast; ring
private theorem evTp_y (z : ℂ) (x y : ℝ) : (Tp .Y).ev z x y = thresholdDeriv y := by
  simp only [Tp,subP,negP,ev,con,ev_powP,thresholdDeriv]; push_cast; ring
private theorem evQ (z : ℂ) (x y : ℝ) : q.ev z x y =
    -(threshold x ^ 2 - 2*rho z*threshold x*threshold y + threshold y ^ 2) /
    (2*denom z) := by
  simp only [q,D,R,subP,negP,ev,con,ev_powP,evT_x,evT_y]
  simp only [div_eq_mul_inv,mul_inv_rev]; ring
private def expr (p : Poly) (z : ℂ) (x y : ℝ) : ℂ := p.ev z x y*Complex.exp (q.ev z x y)
private theorem phiOneExpr (z : ℂ) (x y : ℝ) : phiOne z x y = expr pOne z x y := by
  simp only [phiOne,density,expr,evQ,pOne,subP,negP,E,Z,S,ev,con,id_eq,evTp_x,evTp_y,denom]
  ring
private def dp (d : Poly → Poly) (p : Poly) : Poly := .add (d p) (.mul p (d q))
private theorem exprX (p : Poly) (z : ℂ) (x y : ℝ) :
    HasDerivAt (fun u : ℝ => expr p z u y) (expr (dp dx p) z x y) x := by
  apply ((hdX p z x y).mul (hdX q z x y).cexp).congr_deriv
  simp only [expr,dp,ev]; ring
private theorem exprY (p : Poly) (z : ℂ) (x y : ℝ) :
    HasDerivAt (fun v : ℝ => expr p z x v) (expr (dp dy p) z x y) y := by
  apply ((hdY p z x y).mul (hdY q z x y).cexp).congr_deriv
  simp only [expr,dp,ev]; ring
private theorem exprZ (p : Poly) {z : ℂ} (hz : z ∈ U) (x y : ℝ) :
    HasDerivAt (fun w : ℂ => expr p w x y) (expr (dp dz p) z x y) z := by
  apply ((hdZ p hz x y).mul (hdZ q hz x y).cexp).congr_deriv
  simp only [expr,dp,ev]; ring
private def afterStep (p : Poly) : Poly := .mul Z (subP (dp dz p) (dp dx (dp dy p)))
private theorem step_expr (f : ℂ → ℝ → ℝ → ℂ) (p : Poly)
    (heq : ∀ z ∈ U, ∀ x y, f z x y = expr p z x y) :
    ∀ z ∈ U, ∀ x y, step f z x y = expr (afterStep p) z x y := by
  intro z hz x y
  have he : (fun w : ℂ => f w x y) =ᶠ[𝓝 z] (fun w => expr p w x y) := by
    filter_upwards [openU.eventually_mem hz] with w hw using heq w hw x y
  have heY (a : ℝ) : deriv (f z a) y = expr (dp dy p) z a y := by
    rw [show f z a = fun v => expr p z a v from funext (heq z hz a)]
    exact (exprY p z a y).deriv
  simp only [step,mixed,((exprZ p hz x y).congr_of_eventuallyEq he).deriv,heY,
    (exprX (dp dy p) z x y).deriv]
  simp only [expr,afterStep,subP,negP,Z,ev,con,id_eq]; ring
private def pThree := afterStep (afterStep pOne)
private theorem phiThreeExpr {z : ℂ} (hz : z ∈ U) (x y : ℝ) :
    phiThree z x y = expr pThree z x y :=
  step_expr _ _ (step_expr _ _ (fun w _ a b => phiOneExpr w a b)) z hz x y

private theorem bounds {z : ℂ} (hz : ‖z‖ = 1) : (0.3724 : ℝ) ≤ ‖denom z‖ ∧
    (1/2 : ℝ) ≤ ((denom z)⁻¹).re - |(rho z / denom z).re| := by
  have h := cq_boundary_kernel_bounds z hz
  norm_num [denom,rho] at h ⊢
  exact h
private theorem unitU {z : ℂ} (hz : ‖z‖ = 1) : z ∈ U := by
  have h := (bounds hz).2
  have hr : 0 < ((denom z)⁻¹).re := by linarith only [h,abs_nonneg (rho z/denom z).re]
  rw [inv_re] at hr
  exact mem_slitPlane_iff.mpr (.inl ((div_pos_iff_of_pos_right (normSq_pos.mpr
    (norm_ne_zero_iff.mp (by linarith only [(bounds hz).1])))).mp hr))
private theorem exp_le {z : ℂ} (hz : ‖z‖ = 1) (x y : ℝ) :
    ‖Complex.exp (q.ev z x y)‖ ≤ 1 := by
  let u : ℝ := slope * (x^3-3*x)
  let v : ℝ := slope * (y^3-3*y)
  let a := ((denom z)⁻¹).re
  let b := (rho z / denom z).re
  have h := (bounds hz).2
  change (1/2 : ℝ) ≤ a - |b| at h
  have hep : q.ev z x y = (denom z)⁻¹ * Complex.ofReal (-(u^2+v^2)/2) +
      (rho z/denom z) * Complex.ofReal (u*v) := by
    rw [evQ]
    change -((u:ℂ)^2-2*rho z*(u:ℂ)*(v:ℂ)+(v:ℂ)^2)/(2*denom z)=_
    push_cast; simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [Complex.norm_exp,Real.exp_le_one_iff,hep,add_re,re_mul_ofReal,re_mul_ofReal]
  change a * (-(u^2+v^2)/2)+b*(u*v) ≤ 0
  have H : 2*|u*v| ≤ u^2+v^2 := by
    rw [abs_mul]
    nlinarith only [sq_nonneg (|u|-|v|),sq_abs u,sq_abs v]
  have H' := mul_le_mul_of_nonneg_left H (abs_nonneg b)
  have H'' := mul_le_mul_of_nonneg_right h (add_nonneg (sq_nonneg u) (sq_nonneg v))
  have hr := le_abs_self (b*(u*v))
  rw [abs_mul] at hr
  nlinarith only [H',H'',hr,sq_nonneg u,sq_nonneg v]
private theorem expr_ct (p : Poly) (z : ℂ) : Continuous (fun v : ℝ×ℝ => expr p z v.1 v.2) :=
  (cont p z).mul (Complex.continuous_exp.comp (cont q z))
private theorem expr_bound (p : Poly) {z : ℂ} (hz : ‖z‖ = 1) : ∃ C : ℝ, ∃ k : ℕ,
    0 ≤ C ∧ ∀ x y : ℝ, ‖expr p z x y‖ ≤ C*(weight x y)^k := by
  obtain ⟨C,k,hC,h⟩ := growth p z
  refine ⟨C,k,hC,fun x y => ?_⟩
  rw [expr,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (exp_le hz x y)).trans (h x y)

open MeasureTheory ProbabilityTheory Polynomial
private abbrev γ : Measure ℝ := gaussianReal 0 1
private theorem polyInt (p : ℤ[X]) : Integrable (fun x : ℝ => aeval x p) γ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add,Pi.add_def] using! hp.add hq
  | monomial n a =>
    have hi : Integrable (fun x : ℝ => x^n) γ :=
      integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
        (by simp [γ,integrableExpSet_fun_id_gaussianReal]) n
    simpa only [aeval_monomial] using hi.const_mul ((algebraMap ℤ ℝ) a)
private theorem normLp (p : Poly) {z : ℂ} (hz : ‖z‖ = 1) :
    MemLp (fun t : ℝ×ℝ => expr p z t.1 t.2) 2 (γ.prod γ) := by
  have hct := expr_ct p z
  apply (memLp_two_iff_integrable_sq_norm hct.aestronglyMeasurable).2
  obtain ⟨C,k,hC,h⟩ := expr_bound p hz
  have hi : Integrable (fun u : ℝ => (1+u^2)^(k*2)) γ := by
    convert polyInt ((1+(Polynomial.X : ℤ[X])^2)^(k*2)) using 1
    ext u
    simp
  apply Integrable.mono' ((hi.mul_prod hi).const_mul (C^2)) (hct.norm.pow 2).aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have h' := pow_le_pow_left₀ (norm_nonneg _) (h t.1 t.2) 2
  simpa only [weight,mul_pow,← pow_mul,Pi.pow_apply] using! h'
open MeasureTheory ProbabilityTheory Polynomial
private theorem sphereBound (f : ℂ → ℂ) (hf : ∀ z ∈ U, AnalyticAt ℂ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ = 1 → ‖f z‖ ≤ C := by
  let s := Metric.sphere (0:ℂ) 1
  have h (z : ℂ) (hz : z ∈ s) : ‖z‖ = 1 := by simpa [s,Metric.mem_sphere] using hz
  have hc : ContinuousOn (fun z : ℂ => ‖f z‖) s :=
    fun z hz => ((hf z (unitU (h z hz))).continuousAt.norm).continuousWithinAt
  obtain ⟨B,hB⟩ := (isCompact_sphere (0:ℂ) 1).bddAbove_image hc
  exact ⟨max 0 B,le_max_left _ _, fun z hz => (hB (mem_image_of_mem _ (by simpa [s,Metric.mem_sphere] using hz))).trans (le_max_right _ _)⟩
private theorem uniformGrowth (p : Poly) : ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧
    ∀ z : ℂ, ‖z‖ = 1 → ∀ x y : ℝ, ‖p.ev z x y‖ ≤ C*(weight x y)^k := by
  induction p with
  | coef f h =>
    obtain ⟨C,hC,h⟩ := sphereBound f h
    exact ⟨C,0,hC,fun z hz x y => by simpa only [ev,pow_zero,mul_one] using h z hz⟩
  | X =>
    refine ⟨1,1,zero_le_one,?_⟩
    intro z hz x y
    simp only [ev,norm_real,Real.norm_eq_abs,pow_one,one_mul,weight]
    nlinarith only [sq_nonneg (|x|-1),sq_abs x,sq_nonneg y,mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  | Y =>
    refine ⟨1,1,zero_le_one,?_⟩
    intro z hz x y
    simp only [ev,norm_real,Real.norm_eq_abs,pow_one,one_mul,weight]
    nlinarith only [sq_nonneg (|y|-1),sq_abs y,sq_nonneg x,mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  | add p q hp hq =>
    obtain ⟨A,i,hA,ha⟩ := hp
    obtain ⟨B,j,hB,hb⟩ := hq
    refine ⟨A+B,i+j,add_nonneg hA hB,?_⟩
    intro z hz x y
    apply (norm_add_le _ _).trans
    rw [add_mul]
    exact add_le_add ((ha z hz x y).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (one_weight x y) (by omega : i ≤ i+j)) hA))
      ((hb z hz x y).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (one_weight x y) (by omega : j ≤ i+j)) hB))
  | mul p q hp hq =>
    obtain ⟨A,i,hA,ha⟩ := hp
    obtain ⟨B,j,hB,hb⟩ := hq
    refine ⟨A*B,i+j,mul_nonneg hA hB,?_⟩
    intro z hz x y
    simp only [ev,norm_mul,pow_add]
    have hx := (zero_le_one.trans (one_weight x y))
    calc _ ≤ (A*weight x y^i)*(B*weight x y^j) := mul_le_mul (ha z hz x y) (hb z hz x y) (norm_nonneg _) (mul_nonneg hA (pow_nonneg hx _))
         _ = _ := by ring

private theorem unitNorm (θ : ℝ) : ‖unitPoint θ‖ = 1 := by simp [unitPoint,Complex.norm_exp]
private theorem unitContinuous : Continuous unitPoint := by unfold unitPoint; fun_prop
private theorem angleContinuous (p : Poly) (x y : ℝ) : Continuous (fun θ => p.ev (unitPoint θ) x y) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  exact (p.hdZ (unitU (unitNorm θ)) x y).continuousAt.comp unitContinuous.continuousAt
private theorem energyComponent (p : Poly) : Continuous
    (fun θ : ℝ => ∫ t : ℝ×ℝ, ‖expr p (unitPoint θ) t.1 t.2‖^2 ∂γ.prod γ) := by
  obtain ⟨C,k,hC,h⟩ := uniformGrowth p
  let b (t : ℝ×ℝ) := C^2*((1+t.1^2)^(k*2)*(1+t.2^2)^(k*2))
  have hi : Integrable (fun u : ℝ => (1+u^2)^(k*2)) γ := by
    convert polyInt ((1+(Polynomial.X : ℤ[X])^2)^(k*2)) using 1
    ext u
    simp
  apply continuous_of_dominated (bound := b)
  · intro θ; exact ((expr_ct _ _).norm.pow 2).aestronglyMeasurable
  · intro θ
    apply ae_of_all
    intro t
    have bound : ‖expr p (unitPoint θ) t.1 t.2‖ ≤ C*weight t.1 t.2^k := by
      rw [expr,norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (exp_le (unitNorm θ) _ _)).trans (h _ (unitNorm θ) _ _)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [b,weight,mul_pow,← pow_mul] using pow_le_pow_left₀ (norm_nonneg _) bound 2
  · exact (hi.mul_prod hi).const_mul (C^2)
  · apply ae_of_all
    intro t
    exact ((angleContinuous p _ _).mul (Complex.continuous_exp.comp (angleContinuous q _ _))).norm.pow 2
private theorem mixedExpr (θ x y : ℝ) : mixed (phiThree (unitPoint θ)) x y =
    expr (dp dx (dp dy pThree)) (unitPoint θ) x y := by
  have he : phiThree (unitPoint θ) = fun x y => expr pThree (unitPoint θ) x y :=
    funext fun a => funext fun b => phiThreeExpr (unitU (unitNorm θ)) a b
  rw [he]
  simp only [mixed,(exprY pThree _ _ _).deriv,(exprX (dp dy pThree) _ _ _).deriv]
private theorem energyct : Continuous energy := by
  let P := dp dx (dp dy pThree)
  have he (θ : ℝ) : energy θ = (∫ t : ℝ×ℝ, ‖expr pThree (unitPoint θ) t.1 t.2‖^2 ∂γ.prod γ) +
      4*∫ t : ℝ×ℝ, ‖expr P (unitPoint θ) t.1 t.2‖^2 ∂γ.prod γ := by
    let z := unitPoint θ
    have h1 := (memLp_two_iff_integrable_sq_norm (expr_ct pThree _).aestronglyMeasurable).1 (normLp pThree (unitNorm θ))
    have h2 := (memLp_two_iff_integrable_sq_norm (expr_ct P _).aestronglyMeasurable).1 (normLp P (unitNorm θ))
    have hi : Integrable (fun t : ℝ×ℝ => ‖expr pThree (unitPoint θ) t.1 t.2‖^2+4*‖expr P (unitPoint θ) t.1 t.2‖^2) (γ.prod γ) := h1.add (h2.const_mul 4)
    rw [← integral_const_mul,← integral_add h1 (h2.const_mul 4),integral_prod _ hi]
    simp only [energy,phiThreeExpr (unitU (unitNorm θ)),mixedExpr,P,γ]
  exact continuous_congr he |>.mpr ((energyComponent pThree).add (continuous_const.mul (energyComponent P)))
private def oddKernel (f : ℂ → ℝ → ℝ → ℂ) := ∀ z x y, f (-z) x y = -f z x (-y)
private theorem oddOne : oddKernel phiOne := by
  intro z x y
  have hr : rho (-z) = -rho z := by unfold rho; ring
  have hd : rhoEuler (-z) = -rhoEuler z := by unfold rhoEuler; ring
  have hy : threshold (-y) = -threshold y := by unfold threshold; push_cast; ring
  have hy' : thresholdDeriv (-y) = thresholdDeriv y := by unfold thresholdDeriv; push_cast; ring
  have d (r u v : ℂ) : density (-r) u v = density r u (-v) := by
    unfold density
    rw [show (-r)^2=r^2 by ring,show u^2-2*(-r)*u*v+v^2=u^2-2*r*u*(-v)+(-v)^2 by ring]
  simp only [phiOne,hr,hd,hy,hy',d]; ring
private theorem mixedParity {f : ℂ → ℝ → ℝ → ℂ} (hf : oddKernel f) (z : ℂ) (x y : ℝ) :
    mixed (f (-z)) x y = mixed (f z) x (-y) := by
  have h (a : ℝ) : deriv (f (-z) a) y = deriv (f z a) (-y) := by
    have he : f (-z) a = -(fun t : ℝ => f z a (-t)) := funext (hf z a)
    rw [he,deriv.neg,deriv_comp_neg,neg_neg]
  exact congrArg (fun F : ℝ → ℂ => deriv F x) (funext h)
private theorem oddStep {f : ℂ → ℝ → ℝ → ℂ} (hf : oddKernel f) : oddKernel (step f) := by
  intro z x y
  have he : (fun w : ℂ => f (-w) x y) = -(fun w => f w x (-y)) :=
    funext (fun w => hf w x y)
  have hz := congrArg (fun F : ℂ → ℂ => deriv F z) he
  change deriv (fun w : ℂ => f (-w) x y) z = deriv (-(fun w => f w x (-y))) z at hz
  rw [deriv_comp_neg (fun w : ℂ => f w x y) z,deriv.neg,neg_inj] at hz
  rw [step,step,hz,mixedParity hf]
  ring
private theorem unitShift (θ : ℝ) : unitPoint (θ+Real.pi) = -unitPoint θ := by
  simp only [unitPoint,Complex.ofReal_add,add_mul,Complex.exp_add,Complex.exp_pi_mul_I,mul_neg_one]
private theorem periodicE (θ : ℝ) : energy (θ+Real.pi) = energy θ := by
  have h : oddKernel phiThree := oddStep (oddStep oddOne)
  have hp : MeasurePreserving (fun u : ℝ => -u) γ γ := ⟨by fun_prop,by simp [γ,gaussianReal_map_neg]⟩
  have hm : MeasurableEmbedding (fun u : ℝ => -u) := (Homeomorph.neg ℝ).measurableEmbedding
  have he (x y : ℝ) := h (unitPoint θ) x y
  simp only [energy,unitShift,he,mixedParity h,norm_neg]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  exact hp.integral_comp hm (fun y => ‖phiThree (unitPoint θ) x y‖^2+4*‖mixed (phiThree (unitPoint θ)) x y‖^2)
private theorem halfCircle :
    IntervalIntegrable CQBoundary.energy volume 0 (2*Real.pi) ∧
      (∫ θ in (0:ℝ)..2*Real.pi, CQBoundary.energy θ) = 2*∫ θ in (0:ℝ)..Real.pi, CQBoundary.energy θ := by
  refine ⟨energyct.intervalIntegrable _ _,?_⟩
  have h := intervalIntegral.integral_comp_add_right (a:=0) (b:=Real.pi) energy Real.pi
  simp only [periodicE,zero_add,← two_mul] at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (energyct.intervalIntegrable 0 Real.pi)
    (energyct.intervalIntegrable Real.pi (2*Real.pi)),← h,two_mul]

end KernelRegular

open KernelRegular GrothendieckLB.Supplement MeasureTheory ProbabilityTheory in
theorem solution :
    IntervalIntegrable CQBoundary.energy volume 0 (2*Real.pi) ∧
      (∫ θ in (0:ℝ)..2*Real.pi, CQBoundary.energy θ) = 2*∫ θ in (0:ℝ)..Real.pi, CQBoundary.energy θ := halfCircle
