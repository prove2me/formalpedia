-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_eighth_derivative_le_angular_jets
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:43:53.765965+00:00
-- url     : https://prove2.me/submissions/df5c1cd1-05a4-4608-affb-6966f7099310

import Definitions.Def_GrothendieckLB_Supplement_cqAngularJetNorm
import Definitions.Def_GrothendieckLB_Supplement_cqGaussFourPanel
import Mathlib.Analysis.Calculus.ParametricIntegral
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
open Filter
private def ang (p : Poly) := Poly.mul (.mul (con Complex.I) Z) (dp dz p)
private def F (p : Poly) (L : ℂ →L[ℝ] ℝ) (θ : ℝ) (t : ℝ×ℝ) := L (expr p (unitPoint θ) t.1 t.2)
private theorem angleDer (p : Poly) (L : ℂ →L[ℝ] ℝ) (t : ℝ×ℝ) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => F p L s t) (F (ang p) L θ t) θ := by
  have hc : HasDerivAt unitPoint (unitPoint θ*Complex.I) θ := by
    unfold unitPoint
    simpa using (((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp)
  have he := (exprZ p (unitU (unitNorm θ)) t.1 t.2).scomp θ hc
  apply (L.hasFDerivAt.comp_hasDerivAt θ he).congr_deriv
  simp only [F,ang,expr,ev,con,Z,id_eq,smul_eq_mul]
  congr 1
  ring

private def pair (p q : Poly) (L M : ℂ →L[ℝ] ℝ) (θ : ℝ) (t : ℝ×ℝ) :=
  F p L θ t*F q M θ t
private def J (p q : Poly) (L M : ℂ →L[ℝ] ℝ) (θ : ℝ) := ∫ t : ℝ×ℝ, pair p q L M θ t ∂γ.prod γ

private theorem pairMeas (p q : Poly) (L M : ℂ →L[ℝ] ℝ) (θ : ℝ) :
    AEStronglyMeasurable (pair p q L M θ) (γ.prod γ) :=
  ((L.continuous.comp (expr_ct p _)).mul (M.continuous.comp (expr_ct q _))).aestronglyMeasurable

private theorem angleGrowth (p : Poly) (L : ℂ →L[ℝ] ℝ) :
    ∃ A : ℝ, ∃ k : ℕ, 0 ≤ A ∧ ∀ θ (t : ℝ×ℝ), ‖F p L θ t‖ ≤ A*weight t.1 t.2^k := by
  obtain ⟨C,k,hC,h⟩ := uniformGrowth p
  refine ⟨‖L‖*C,k,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro θ t
  unfold F
  apply (L.le_opNorm _).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [expr,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (exp_le (unitNorm θ) _ _)).trans (h _ (unitNorm θ) _ _)

private theorem pairDom (p q : Poly) (L M : ℂ →L[ℝ] ℝ) :
    ∃ b : ℝ×ℝ → ℝ, Integrable b (γ.prod γ) ∧ ∀ θ t, ‖pair p q L M θ t‖ ≤ b t := by
  obtain ⟨A,i,hA,ha⟩ := angleGrowth p L
  obtain ⟨B,j,hB,hb⟩ := angleGrowth q M
  have hi : Integrable (fun u : ℝ => (1+u^2)^(i+j)) γ := by
    convert polyInt ((1+(Polynomial.X : ℤ[X])^2)^(i+j)) using 1
    ext u
    simp
  refine ⟨fun t => (A*B)*((1+t.1^2)^(i+j)*(1+t.2^2)^(i+j)),(hi.mul_prod hi).const_mul (A*B),?_⟩
  intro θ t
  have hn := zero_le_one.trans (one_weight t.1 t.2)
  have h := mul_le_mul (ha θ t) (hb θ t) (norm_nonneg _) (mul_nonneg hA (pow_nonneg hn i))
  rw [pair,norm_mul]
  refine h.trans_eq ?_
  simp only [weight,mul_pow,pow_add]
  ring

private theorem pairInt (p q : Poly) (L M : ℂ →L[ℝ] ℝ) (θ : ℝ) :
    Integrable (pair p q L M θ) (γ.prod γ) := by
  obtain ⟨b,hi,hb⟩ := pairDom p q L M
  exact hi.mono' (pairMeas p q L M θ) (ae_of_all _ (hb θ))

private theorem JD (p q : Poly) (L M : ℂ →L[ℝ] ℝ) (θ : ℝ) :
    HasDerivAt (J p q L M) (J (ang p) q L M θ+J p (ang q) L M θ) θ := by
  obtain ⟨b,hi,hb⟩ := pairDom (ang p) q L M
  obtain ⟨c,hj,hc⟩ := pairDom p (ang q) L M
  let g (u : ℝ) := pair (ang p) q L M u + pair p (ang q) L M u
  have hgi := (pairInt (ang p) q L M θ).add (pairInt p (ang q) L M θ)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=pair p q L M) (F':=g)
    (μ:=γ.prod γ) (s:=Set.univ) (bound:=b+c) (Filter.univ_mem : Set.univ ∈ 𝓝 θ)
    (Filter.Eventually.of_forall (pairMeas p q L M)) (pairInt p q L M θ) hgi.aestronglyMeasurable
    (ae_of_all _ (fun t w _ => (norm_add_le _ _).trans (add_le_add (hb w t) (hc w t))))
    (hi.add hj) (ae_of_all _ (fun t w _ => (angleDer p L t w).mul (angleDer q M t w)))
  simpa only [g,Pi.add_apply,integral_add (pairInt (ang p) q L M θ) (pairInt p (ang q) L M θ),J] using! hd.2

private theorem smoothJ (n : ℕ) (p q : Poly) (L M : ℂ →L[ℝ] ℝ) : ContDiff ℝ n (J p q L M) := by
  have h : Differentiable ℝ (J p q L M) := fun θ => (JD p q L M θ).differentiableAt
  induction n generalizing p q with
  | zero => exact contDiff_zero.mpr h.continuous
  | succ n ih =>
    rw [Nat.cast_succ,contDiff_succ_iff_deriv]
    refine ⟨h,by simp,?_⟩
    have he : deriv (J p q L M)=J (ang p) q L M + J p (ang q) L M :=
      funext (fun θ => (JD p q L M θ).deriv)
    rw [he]
    exact (ih (ang p) q (fun θ => (JD _ _ L M θ).differentiableAt)).add
      (ih p (ang q) (fun θ => (JD _ _ L M θ).differentiableAt))

private theorem smoothSq (p : Poly) (n : ℕ) : ContDiff ℝ n
    (fun θ : ℝ => ∫ t : ℝ×ℝ, ‖expr p (unitPoint θ) t.1 t.2‖^2 ∂γ.prod γ) := by
  have h : (fun θ : ℝ => ∫ t : ℝ×ℝ, ‖expr p (unitPoint θ) t.1 t.2‖^2 ∂γ.prod γ)=
      J p p Complex.reCLM Complex.reCLM+J p p Complex.imCLM Complex.imCLM := by
    ext θ
    rw [Pi.add_apply,J,J,←integral_add (pairInt _ _ _ _ θ) (pairInt _ _ _ _ θ)]
    apply integral_congr_ae
    apply ae_of_all
    intro t
    simp only [pair,F,Complex.reCLM_apply,Complex.imCLM_apply,Complex.sq_norm,Complex.normSq_apply]
  rw [h]
  exact (smoothJ n ..).add (smoothJ n ..)

private theorem smoothEnergy : ContDiff ℝ 8 energy := by
  let P := dp dx (dp dy pThree)
  have he (θ : ℝ) : energy θ = (∫ t : ℝ×ℝ, ‖expr pThree (unitPoint θ) t.1 t.2‖^2 ∂γ.prod γ) +
      4*∫ t : ℝ×ℝ, ‖expr P (unitPoint θ) t.1 t.2‖^2 ∂γ.prod γ := by
    let z := unitPoint θ
    have h1 := (memLp_two_iff_integrable_sq_norm (expr_ct pThree _).aestronglyMeasurable).1 (normLp pThree (unitNorm θ))
    have h2 := (memLp_two_iff_integrable_sq_norm (expr_ct P _).aestronglyMeasurable).1 (normLp P (unitNorm θ))
    have hi : Integrable (fun t : ℝ×ℝ => ‖expr pThree (unitPoint θ) t.1 t.2‖^2+4*‖expr P (unitPoint θ) t.1 t.2‖^2) (γ.prod γ) := h1.add (h2.const_mul 4)
    rw [← integral_const_mul,← integral_add h1 (h2.const_mul 4),integral_prod _ hi]
    simp only [energy,phiThreeExpr (unitU (unitNorm θ)),mixedExpr,P,γ]
  rw [funext he]
  exact (smoothSq pThree 8).add (contDiff_const.mul (smoothSq P 8))
private theorem panels (i : ℕ) : ContDiff ℝ 8 (GaussFour.panel i) :=
  smoothEnergy.comp (show ContDiff ℝ 8 (fun x : ℝ => (i:ℝ)*(Real.pi/1024)+(Real.pi/1024)*x) by fun_prop)

end KernelRegular
open GrothendieckLB.Supplement CQBoundary MeasureTheory ProbabilityTheory Complex Set
open scoped Topology
namespace KernelRegular
open Poly

private def vector (p : Poly) (θ : ℝ) (t : ℝ×ℝ) := expr p (unitPoint θ) t.1 t.2
private def sizeK (p : Poly) (θ : ℝ) := Real.sqrt (∫ t, ‖vector p θ t‖^2 ∂γ.prod γ)
private def corrK (p q : Poly) := J p q reCLM reCLM + J p q imCLM imCLM
private def powers : ℕ → Poly → Poly
  | 0,p => p
  | n+1,p => powers n (ang p)

private theorem angD (p : Poly) (θ : ℝ) (t : ℝ×ℝ) :
    HasDerivAt (fun a => vector p a t) (vector (ang p) θ t) θ := by
  have hc : HasDerivAt unitPoint (unitPoint θ*I) θ := by
    unfold unitPoint
    simpa using (((hasDerivAt_id θ).ofReal_comp.mul_const I).cexp)
  apply ((exprZ p (unitU (unitNorm θ)) t.1 t.2).scomp θ hc).congr_deriv
  simp only [vector,ang,expr,ev,con,Z,id_eq,smul_eq_mul]
  ring

private theorem vectIter (n : ℕ) (p : Poly) (t : ℝ×ℝ) :
    iteratedDeriv n (fun a => vector p a t) = fun a => vector (powers n p) a t := by
  induction n generalizing p with
  | zero => simp [powers]
  | succ n ih =>
    rw [iteratedDeriv_succ',show deriv (fun a => vector p a t)=fun a => vector (ang p) a t from
      funext (fun a => (angD p a t).deriv)]
    exact ih (ang p)

private theorem corrKD (p q : Poly) :
    deriv (corrK p q)=corrK (ang p) q + corrK p (ang q) := by
  funext θ
  have h := ((JD p q reCLM reCLM θ).add (JD p q imCLM imCLM θ)).deriv
  simpa only [corrK,Pi.add_apply,add_add_add_comm] using h

private theorem corrSmooth (n : ℕ) (p q : Poly) : ContDiff ℝ n (corrK p q) :=
  (smoothJ n ..).add (smoothJ n ..)

private theorem corrIter (n : ℕ) (p q : Poly) (θ : ℝ) :
    iteratedDeriv n (corrK p q) θ=
      ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*corrK (powers j p) (powers (n-j) q) θ := by
  induction n generalizing p q with
  | zero => simp [powers]
  | succ n ih =>
    rw [iteratedDeriv_succ',corrKD,iteratedDeriv_add (corrSmooth n ..).contDiffAt
      (corrSmooth n ..).contDiffAt,ih,ih]
    rw [Finset.sum_choose_succ_mul (fun i j => corrK (powers i p) (powers j q) θ) n]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have e : n+1-j = (n-j)+1 := by have := Finset.mem_range.mp hj; omega
    rw [e]
    rfl

private theorem corrBound (p q : Poly) (θ : ℝ) :
    corrK p q θ ≤ sizeK p θ * sizeK q θ := by
  have hp : MemLp (vector p θ) 2 (γ.prod γ) := normLp p (unitNorm θ)
  have hq : MemLp (vector q θ) 2 (γ.prod γ) := normLp q (unitNorm θ)
  have ht := integral_mul_norm_le_Lp_mul_Lq (μ:=γ.prod γ) Real.HolderConjugate.two_two
    (show MemLp (vector p θ) (ENNReal.ofReal (2:ℝ)) (γ.prod γ) by simpa using hp)
    (show MemLp (vector q θ) (ENNReal.ofReal (2:ℝ)) (γ.prod γ) by simpa using hq)
  have h1 := pairInt p q reCLM reCLM θ
  have h2 := pairInt p q imCLM imCLM θ
  unfold corrK
  rw [Pi.add_apply,J,J,←integral_add h1 h2]
  refine (integral_mono (h1.add h2) (hp.norm.integrable_mul hq.norm) (fun t => ?_)).trans ?_
  · have h := Complex.re_le_norm ((vector p θ t)*(starRingEnd ℂ (vector q θ t)))
    simpa only [Pi.add_apply,pair,F,vector,Complex.reCLM_apply,Complex.imCLM_apply,
      Complex.mul_re,Complex.conj_re,Complex.conj_im,mul_neg,sub_neg_eq_add,norm_mul,Complex.norm_conj] using! h
  · simpa only [Pi.mul_apply,sizeK,Real.sqrt_eq_rpow,Real.rpow_two] using! ht

private theorem squareCorr (p : Poly) (θ : ℝ) :
    corrK p p θ=∫ t, ‖vector p θ t‖^2 ∂γ.prod γ := by
  rw [corrK,Pi.add_apply,J,J,←integral_add (pairInt _ _ _ _ θ) (pairInt _ _ _ _ θ)]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [pair,F,Pi.add_apply,vector,Complex.reCLM_apply,Complex.imCLM_apply,Complex.sq_norm,Complex.normSq_apply]

private def space (b : Bool) := if b then dp dx (dp dy pThree) else pThree
private theorem realJet (b : Bool) (n : ℕ) (θ : ℝ) :
    sizeK (powers n (space b)) θ=angularJetNorm b n θ := by
  unfold sizeK angularJetNorm
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  rw [←congrFun (vectIter n (space b) t) θ]
  congr 2
  apply congrArg (fun f : ℝ → ℂ => iteratedDeriv n f θ)
  funext a
  cases b
  · exact (phiThreeExpr (unitU (unitNorm a)) t.1 t.2).symm
  · exact (mixedExpr a t.1 t.2).symm

private theorem energyC : energy = corrK (space false) (space false) +
    (fun θ => 4*corrK (space true) (space true) θ) := by
  funext θ
  rw [Pi.add_apply,squareCorr,squareCorr]
  let P := dp dx (dp dy pThree)
  have h1 := (memLp_two_iff_integrable_sq_norm (expr_ct pThree _).aestronglyMeasurable).1 (normLp pThree (unitNorm θ))
  have h2 := (memLp_two_iff_integrable_sq_norm (expr_ct P _).aestronglyMeasurable).1 (normLp P (unitNorm θ))
  have hi : Integrable (fun t : ℝ×ℝ => ‖expr pThree (unitPoint θ) t.1 t.2‖^2+4*‖expr P (unitPoint θ) t.1 t.2‖^2) (γ.prod γ) := h1.add (h2.const_mul 4)
  change energy θ = (∫ t, ‖expr pThree (unitPoint θ) t.1 t.2‖^2 ∂γ.prod γ) + 4*(∫ t, ‖expr P (unitPoint θ) t.1 t.2‖^2 ∂γ.prod γ)
  rw [←integral_const_mul,←integral_add h1 (h2.const_mul 4),integral_prod _ hi]
  simp only [energy,phiThreeExpr (unitU (unitNorm θ)),mixedExpr,P,γ]

private theorem jetBound (θ : ℝ) : iteratedDeriv 8 energy θ ≤
    jetMajorant (fun b j => angularJetNorm b j θ) := by
  rw [energyC,iteratedDeriv_add (corrSmooth 8 ..).contDiffAt
    (contDiff_const.mul (corrSmooth 8 ..)).contDiffAt,iteratedDeriv_const_mul_field,
    corrIter,corrIter,jetMajorant,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h0 := corrBound (powers j (space false)) (powers (8-j) (space false)) θ
  have h1 := corrBound (powers j (space true)) (powers (8-j) (space true)) θ
  rw [realJet,realJet] at h0 h1
  calc _ = ((8:ℕ).choose j:ℝ)*(_+4*_) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h0 (mul_le_mul_of_nonneg_left h1 (by norm_num))) (Nat.cast_nonneg _)

private theorem panelJet (i : ℕ) (x : ℝ) :
    iteratedDeriv 8 (GaussFour.panel i) x ≤ (Real.pi/1024)^8 *
      jetMajorant (fun b j => angularJetNorm b j ((i:ℝ)*(Real.pi/1024)+(Real.pi/1024)*x)) := by
  let d := Real.pi/1024
  let a := (i:ℝ)*d
  let g : ℝ → ℝ := fun y => energy (a+y)
  have hg : ContDiff ℝ 8 g := smoothEnergy.comp (contDiff_const.add contDiff_id)
  change iteratedDeriv 8 (fun y => g (d*y)) x ≤ d^8*_
  rw [iteratedDeriv_comp_const_mul hg d]
  have hz : iteratedDeriv 8 g (d*x)=iteratedDeriv 8 energy (a+d*x) :=
    congrFun (iteratedDeriv_comp_const_add 8 energy a) (d*x)
  change d^8*iteratedDeriv 8 g (d*x) ≤ _
  rw [hz]
  exact mul_le_mul_of_nonneg_left (jetBound (a+d*x)) (by dsimp [d]; positivity)

end KernelRegular

open KernelRegular in
theorem solution :
    ∀ (i : ℕ) (x : ℝ), iteratedDeriv 8 (GaussFour.panel i) x ≤ (Real.pi/1024)^8 *
      jetMajorant (fun b j => angularJetNorm b j ((i:ℝ)*(Real.pi/1024)+(Real.pi/1024)*x)) := panelJet
