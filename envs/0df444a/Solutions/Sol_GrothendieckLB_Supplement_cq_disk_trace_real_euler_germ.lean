-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_disk_trace_real_euler_germ
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:26:53.579542+00:00
-- url     : https://prove2.me/submissions/66ee267b-cf64-473d-a776-4371dc33382d

import Theorems.Thm_GrothendieckLB_Supplement_cq_first_euler_gaussian_price
import Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_hermite_expansion
import Definitions.Def_GrothendieckLB_taylorCoeff
import Mathlib.Analysis.Analytic.Uniqueness
import Theorems.Thm_GrothendieckLB_Supplement_gaussian_hermite_diagonal_bessel
import Definitions.Def_GrothendieckLB_Supplement_cqDiskEulerTrace
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Theorems.Thm_GrothendieckLB_Supplement_gaussian_hermite_integration_by_parts
import Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel
import Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_kernel_bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib

open GrothendieckLB.Supplement CQBoundary Complex Set
open scoped Topology
set_option maxHeartbeats 1400000
open GrothendieckLB GrothendieckLB.Supplement Polynomial Real Filter FormalMultilinearSeries
open MeasureTheory
open scoped Topology
namespace CubicTaylor
set_option maxHeartbeats 500000

private theorem rho_dvd (u v : ℝ) : X ∣ cqRhoPoly u v := by
  apply X_dvd_iff.mpr
  simp [cqRhoPoly,coeff_mul_X_pow',coeff_X_pow]

private theorem rho_coeff (u v : ℝ) (a j : ℕ) : |((cqRhoPoly u v)^a).coeff j| ≤ 1 := by
  let ρ := cqRhoPoly u v
  let D : ℝ := 1+u^2+v^2
  have hD : 0 < D := by dsimp [D]; positivity
  change |(ρ^a).coeff j| ≤ 1
  induction a generalizing j with
  | zero => simp [Polynomial.coeff_one]; split <;> norm_num
  | succ a ih =>
    let s (k : ℕ) := if k ≤ j then (ρ^a).coeff (j-k) else 0
    have hb (k : ℕ) : |s k| ≤ 1 := by unfold s; split <;> simp_all
    have hs : ρ^(a+1) = C (1/D) * ((ρ^a * X^1) - C (u^2) * (ρ^a * X^3) + C (v^2) * (ρ^a * X^5)) := by
      rw [pow_succ]
      change ρ^a * (C (1/D) * (X-C (u^2)*X^3+C (v^2)*X^5)) = _
      ring
    rw [hs,coeff_C_mul,coeff_add,coeff_sub,coeff_C_mul,coeff_C_mul]
    simp only [coeff_mul_X_pow']
    change |1/D*(s 1-u^2*s 3+v^2*s 5)| ≤ 1
    rw [abs_mul,abs_of_pos (one_div_pos.mpr hD),one_div,mul_comm,←div_eq_mul_inv,div_le_iff₀ hD,one_mul]
    calc _ ≤ |s 1-u^2*s 3|+|v^2*s 5| := abs_add_le _ _
         _ ≤ (|s 1|+|u^2*s 3|)+|v^2*s 5| := add_le_add_left (abs_sub _ _) _
         _ ≤ D := by
           simp only [abs_mul,abs_of_nonneg (sq_nonneg u),abs_of_nonneg (sq_nonneg v)]
           dsimp only [D]
           nlinarith only [hb 1,mul_nonneg (sq_nonneg u) (sub_nonneg.mpr (hb 3)),mul_nonneg (sq_nonneg v) (sub_nonneg.mpr (hb 5))]

private noncomputable def q (η u v : ℝ) (p : ℕ × ℕ) : ℝ[X] :=
  C (Real.pi/2*(-1:ℝ)^p.2*(cqA η u v p.1 p.2)^2) * ((cqRhoPoly u v)^p.1*X^p.2)

private theorem q_zero (η u v : ℝ) (p : ℕ × ℕ) {m : ℕ} (hm : m < p.1+p.2) :
    (q η u v p).coeff m = 0 := by
  apply (X_pow_dvd_iff (n:=p.1+p.2)).mp _ m hm
  obtain ⟨Q,hQ⟩ := rho_dvd u v
  refine ⟨C (Real.pi/2*(-1:ℝ)^p.2*(cqA η u v p.1 p.2)^2)*Q^p.1,?_⟩
  rw [q,hQ,mul_pow,pow_add]
  ring

private theorem q_bound (η u v : ℝ) (p : ℕ × ℕ) (m : ℕ) : |(q η u v p).coeff m| ≤ Real.pi/2 := by
  have hA := (cq_gaussian_hermite_expansion η u v).2 p.1 p.2
  simp only [q,coeff_C_mul,coeff_mul_X_pow',abs_mul,abs_pow,abs_neg,abs_one,one_pow,mul_one,
    abs_of_nonneg (by positivity : 0 ≤ Real.pi/2)]
  split
  · apply mul_le_of_le_one_right (by positivity) (rho_coeff u v _ _) |>.trans
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (abs_nonneg _) hA)
  · simp; positivity

private def box (m : ℕ) := Finset.range (m+1) ×ˢ Finset.range (m+1)

private theorem outside {p : ℕ × ℕ} {m : ℕ} (hp : p ∉ box m) : m < p.1+p.2 := by
  by_contra! h
  exact hp (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩)

private noncomputable def coef (η u v : ℝ) (m : ℕ) : ℝ := ∑ p ∈ box m, (q η u v p).coeff m

private theorem row_bound (η u v : ℝ) (m : ℕ) :
    (∑ p ∈ box m, |(q η u v p).coeff m|) ≤ (Real.pi/2)*(((m:ℝ)+1)^2) := by
  calc _ ≤ ∑ _p ∈ box m, (Real.pi/2) := Finset.sum_le_sum (fun p _ => q_bound η u v p m)
       _ = _ := by simp [box,Finset.card_product,nsmul_eq_mul,pow_two]; ring

private theorem eval_row (η u v t : ℝ) (p : ℕ × ℕ) :
    HasSum (fun m : ℕ => (q η u v p).coeff m*t^m)
      (Real.pi/2*(cqA η u v p.1 p.2)^2*((cqRhoPoly u v).eval t)^p.1*(-t)^p.2) := by
  have z (n : ℕ) (hn : n ∉ (q η u v p).support) : (q η u v p).coeff n*t^n=0 :=
    by rw [Polynomial.notMem_support_iff.mp hn,zero_mul]
  have hs : HasSum (fun n => (q η u v p).coeff n*t^n) (∑ n ∈ (q η u v p).support,(q η u v p).coeff n*t^n) := hasSum_sum_of_ne_finset_zero z
  rw [show (∑ n ∈ (q η u v p).support, (q η u v p).coeff n*t^n) = (q η u v p).eval t from (eval_eq_sum (p:=q η u v p) (x:=t)).symm] at hs
  have he : (q η u v p).eval t = Real.pi/2*(cqA η u v p.1 p.2)^2*((cqRhoPoly u v).eval t)^p.1*(-t)^p.2 := by
    simp only [q,eval_mul,eval_C,eval_pow,eval_X]
    rw [show -t=(-1)*t by ring,mul_pow]
    ring
  exact he ▸ hs

private theorem coefficient_hasSum (η u v t : ℝ) (ht : |t| < 1) :
    HasSum (fun m => coef η u v m*t^m) (cqCorr η u v t) := by
  let F (z : ℕ × (ℕ × ℕ)) := (q η u v z.2).coeff z.1*t^z.1
  have hz (m : ℕ) (p : ℕ × ℕ) (hp : p ∉ box m) : F (m,p)=0 := by simp [F,q_zero η u v p (outside hp)]
  have hb (m : ℕ) : (∑' p : ℕ × ℕ, |F (m,p)|) ≤ (Real.pi/2)*(((m:ℝ)+1)^2)*|t|^m := by
    rw [tsum_eq_sum (s:=box m) (fun p hp => by simp [hz m p hp])]
    simp only [F,abs_mul,abs_pow,← Finset.sum_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (row_bound η u v m) (by positivity)
  have htn : ‖|t|‖ < 1 := by simpa only [Real.norm_eq_abs,abs_abs] using ht
  have geom (k : ℕ) : Summable (fun m : ℕ => (m:ℝ)^k*|t|^m) := summable_pow_mul_geometric_of_norm_lt_one k htn
  have hg : Summable (fun m : ℕ => (Real.pi/2)*(((m:ℝ)+1)^2)*|t|^m) := by
    apply (((geom 2).add ((geom 1).mul_left 2)).add (geom 0) |>.mul_left (Real.pi/2)).congr
    intro m
    change (Real.pi/2)*(((m:ℝ)^2*|t|^m+2*((m:ℝ)^1*|t|^m))+(m:ℝ)^0*|t|^m)=_
    ring
  have habs : Summable (fun z => |F z|) := by
    apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
    refine ⟨fun m => summable_of_ne_finset_zero (s:=box m) (fun p hp => by simp [hz m p hp]),?_⟩
    exact Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => abs_nonneg _)) hb hg
  have hs : Summable F := habs.of_norm
  have hrow (m : ℕ) : HasSum (fun p => F (m,p)) (coef η u v m*t^m) := by
    simpa only [F,coef,Finset.sum_mul] using hasSum_sum_of_ne_finset_zero (hz m)
  have hcol := (hs.prod_symm.hasSum).prod_fiberwise (fun p => eval_row η u v t p)
  have hspec := (cq_gaussian_hermite_expansion η u v).1 t ht
  have htgt := hcol.unique hspec
  have htotal : (∑' p, F p)=cqCorr η u v t := by
    calc _ = ∑' p : (ℕ × ℕ) × ℕ, F p.swap := ((Equiv.prodComm (ℕ × ℕ) ℕ).tsum_eq F).symm
         _ = _ := htgt
  exact htotal ▸ hs.hasSum.prod_fiberwise hrow

private theorem corr_analytic (η u v : ℝ) : AnalyticAt ℝ (cqCorr η u v) 0 := by
  let c := coef η u v
  let H := cqCorr η u v
  have hseries : HasFPowerSeriesAt H (ofScalars ℝ c) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    have hn : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
    filter_upwards [hn] with t ht
    simpa only [c,H,coeff_ofScalars,zero_add,smul_eq_mul,mul_comm] using coefficient_hasSum η u v t ht
  exact hseries.analyticAt

end CubicTaylor

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
private theorem smallRho {z : ℂ} (hz : ‖z‖ < 1) : ‖rho z‖ < 1 := by
  let a : ℝ := 0.34101124^2
  let b : ℝ := 0.05276111^2
  let V : ℝ := 1+a+b
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hV : 0 < V := by dsimp [V]; positivity
  have he : rho z = (z-(a:ℂ)*z^3+(b:ℂ)*z^5)/(V:ℂ) := by norm_num [rho,V,a,b]
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV,div_lt_one hV]
  calc
    _ ≤ (‖z‖+‖(a:ℂ)*z^3‖)+‖(b:ℂ)*z^5‖ :=
      (norm_add_le ..).trans (add_le_add_left (norm_sub_le ..) _)
    _ < V := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,V]
      have h3 : ‖z‖^3 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz.le
      have h5 : ‖z‖^5 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz.le
      nlinarith only [hz,mul_le_mul_of_nonneg_left h3 ha,mul_le_mul_of_nonneg_left h5 hb]
private theorem recip {w : ℂ} (hw : ‖w‖ < 1) : (1/2 : ℝ) ≤ ((1-w)⁻¹).re := by
  have hne : 1-w ≠ 0 := by intro hh; rw [← sub_eq_zero.mp hh,norm_one] at hw; exact (lt_irrefl _ hw)
  have hn : normSq w ≤ 1 := by
    rw [normSq_eq_norm_sq]; exact pow_le_one₀ (norm_nonneg _) hw.le
  rw [inv_re, le_div_iff₀ (normSq_pos.mpr hne)]
  simp only [normSq_apply,sub_re,one_re,sub_im,one_im,zero_sub,neg_mul_neg] at hn ⊢
  linarith only [hn]
private theorem diskQuad {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (1/2 : ℝ) ≤ ((denom z)⁻¹).re - |(rho z/denom z).re| := by
  rcases lt_or_eq_of_le hz with h|h
  · let r := rho z
    have hr : ‖r‖ < 1 := smallRho h
    have h1 : 1-r ≠ 0 := by intro hh; rw [← sub_eq_zero.mp hh,norm_one] at hr; exact lt_irrefl _ hr
    have h2 : 1+r ≠ 0 := by
      intro hh; have he : r = -1 := by linear_combination hh
      rw [he,norm_neg,norm_one] at hr; exact lt_irrefl _ hr
    have hd : 1-r^2 ≠ 0 := by rw [show 1-r^2=(1-r)*(1+r) by ring]; exact mul_ne_zero h1 h2
    have hl : (1-r^2)⁻¹+r/(1-r^2)=(1-r)⁻¹ := by field_simp; ring
    have hu : (1-r^2)⁻¹-r/(1-r^2)=(1+r)⁻¹ := by field_simp; ring
    have hp := recip hr
    have hm := recip (w := -r) (by simpa only [norm_neg] using hr)
    rw [sub_neg_eq_add,← hu,sub_re] at hm
    rw [← hl,add_re] at hp
    change (1/2 : ℝ) ≤ ((1-r^2)⁻¹).re - |(r/(1-r^2)).re|
    rw [le_sub_comm,abs_le]; constructor <;> linarith only [hm,hp]
  · exact (bounds h).2
private theorem diskU {z : ℂ} (hz : ‖z‖ ≤ 1) : z ∈ U := by
  have h := diskQuad hz
  have hr : 0 < ((denom z)⁻¹).re := by linarith only [h,abs_nonneg (rho z/denom z).re]
  have hd : denom z ≠ 0 := by intro hh; simp [hh] at hr
  rw [inv_re] at hr
  exact mem_slitPlane_iff.mpr (.inl ((div_pos_iff_of_pos_right (normSq_pos.mpr hd)).mp hr))
private theorem exp_le {z : ℂ} (hz : ‖z‖ ≤ 1) (x y : ℝ) :
    ‖Complex.exp (q.ev z x y)‖ ≤ 1 := by
  let u : ℝ := slope * (x^3-3*x)
  let v : ℝ := slope * (y^3-3*y)
  let a := ((denom z)⁻¹).re
  let b := (rho z / denom z).re
  have h := diskQuad hz
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
private theorem expr_bound (p : Poly) {z : ℂ} (hz : ‖z‖ ≤ 1) : ∃ C : ℝ, ∃ k : ℕ,
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
private theorem normLp (p : Poly) {z : ℂ} (hz : ‖z‖ ≤ 1) :
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
private def H (n : ℕ) (x : ℝ) := Complex.ofReal (QuadSDE.hermiteN n x)
private def A (p : Poly) (z : ℂ) (m n : ℕ) (x y : ℝ) := expr p z x y * H m x * H n y
private theorem hermSquare (n : ℕ) : Integrable (fun x : ℝ => (QuadSDE.hermiteN n x)^2) γ := by
  have hi := (polyInt (Polynomial.hermite n ^ 2)).div_const ((Real.sqrt (n.factorial:ℝ))^2)
  simpa only [QuadSDE.hermiteN,div_pow,map_pow] using hi
private theorem integrableA (p : Poly) {z : ℂ} (hz : ‖z‖ ≤ 1) (m n : ℕ) :
    Integrable (fun v : ℝ×ℝ => A p z m n v.1 v.2) (γ.prod γ) := by
  let h (t : ℝ×ℝ) := H m t.1 * H n t.2
  have hm : Continuous h := by unfold h H QuadSDE.hermiteN; fun_prop
  have hL : MemLp h 2 (γ.prod γ) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    simpa only [h,H,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
      using (hermSquare m).mul_prod (hermSquare n)
  simpa only [A,h,mul_assoc,Pi.mul_def] using! (normLp p hz).integrable_mul hL
private theorem joint_bound (p q' : Poly) {z : ℂ} (hz : ‖z‖ ≤ 1) : ∃ C : ℝ, ∃ k : ℕ,
    ∀ x y : ℝ, ‖expr p z x y‖+‖expr q' z x y‖ ≤ C*(weight x y)^k := by
  obtain ⟨A',i,hA,ha⟩ := expr_bound p hz
  obtain ⟨B,j,hB,hb⟩ := expr_bound q' hz
  refine ⟨A'+B,i+j,fun x y => ?_⟩
  rw [add_mul]
  exact add_le_add ((ha x y).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (one_weight x y) (by omega : i ≤ i+j)) hA))
    ((hb x y).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (one_weight x y) (by omega : j ≤ i+j)) hB))
private def sN (n : ℕ) := Complex.ofReal (Real.sqrt (n+1:ℝ))
private theorem raiseX (p : Poly) {z : ℂ} (hz : ‖z‖ ≤ 1) (n j : ℕ) (y : ℝ) :
    (∫ x, A (dp dx p) z n j x y ∂γ) = sN n * ∫ x, A p z (n+1) j x y ∂γ := by
  obtain ⟨C,k,h⟩ := joint_bound p (dp dx p) hz
  have hb (x : ℝ) : ‖expr p z x y‖+‖expr (dp dx p) z x y‖ ≤ (C*(1+y^2)^k)*(1+x^2)^k := by
    convert h x y using 1; simp only [weight,mul_pow]; ring
  have hi := gaussian_hermite_integration_by_parts (fun x => expr p z x y) (fun x => expr (dp dx p) z x y)
    ((expr_ct _ _).comp (continuous_id.prodMk continuous_const)) (fun x => exprX p z x y) _ _ hb n
  change (∫ x, expr (dp dx p) z x y*H n x ∂γ) = sN n * ∫ x, expr p z x y*H (n+1) x ∂γ at hi
  simp only [A,integral_mul_const,hi]
  ring
private theorem raiseY (p : Poly) {z : ℂ} (hz : ‖z‖ ≤ 1) (i n : ℕ) (x : ℝ) :
    (∫ y, A (dp dy p) z i n x y ∂γ) = sN n * ∫ y, A p z i (n+1) x y ∂γ := by
  obtain ⟨C,k,h⟩ := joint_bound p (dp dy p) hz
  have hb (y : ℝ) : ‖expr p z x y‖+‖expr (dp dy p) z x y‖ ≤ (C*(1+x^2)^k)*(1+y^2)^k := by
    convert h x y using 1; simp only [weight,mul_pow]; ring
  have hi := gaussian_hermite_integration_by_parts (expr p z x) (expr (dp dy p) z x)
    ((expr_ct _ _).comp (continuous_const.prodMk continuous_id)) (fun y => exprY p z x y) _ _ hb n
  change (∫ y, expr (dp dy p) z x y*H n y ∂γ) = sN n * ∫ y, expr p z x y*H (n+1) y ∂γ at hi
  have e (p' : Poly) (m : ℕ) (y : ℝ) : A p' z i m x y = (expr p' z x y*H m y)*H i x := mul_right_comm _ _ _
  simp only [e,integral_mul_const,hi]
  ring

private theorem sphereBound (f : ℂ → ℂ) (hf : ∀ z ∈ U, AnalyticAt ℂ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ C := by
  let s := Metric.closedBall (0:ℂ) 1
  have h (z : ℂ) (hz : z ∈ s) : ‖z‖ ≤ 1 := by simpa [s,Metric.mem_closedBall] using hz
  have hc : ContinuousOn (fun z : ℂ => ‖f z‖) s :=
    fun z hz => ((hf z (diskU (h z hz))).continuousAt.norm).continuousWithinAt
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) 1).bddAbove_image hc
  exact ⟨max 0 B,le_max_left _ _, fun z hz => (hB (mem_image_of_mem _ (by simpa [s,Metric.mem_closedBall] using hz))).trans (le_max_right _ _)⟩
private theorem uniformGrowth (p : Poly) : ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧
    ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ x y : ℝ, ‖p.ev z x y‖ ≤ C*(weight x y)^k := by
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

private def coeff (p : Poly) (n : ℕ) (z : ℂ) := ∫ t : ℝ×ℝ, A p z n n t.1 t.2 ∂γ.prod γ
private def xy (p : Poly) := dp dx (dp dy p)
private theorem coeff_shift (p : Poly) (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    coeff (xy p) n z = ((n:ℂ)+1)*coeff p (n+1) z := by
  unfold coeff xy
  rw [integral_prod_symm _ (integrableA _ hz _ _)]
  simp only [raiseX _ hz,integral_const_mul]
  rw [← integral_prod_symm _ (integrableA (dp dy p) hz (n+1) n),
    integral_prod _ (integrableA (dp dy p) hz (n+1) n),integral_prod _ (integrableA p hz (n+1) (n+1))]
  simp only [raiseY _ hz,integral_const_mul,← mul_assoc]
  congr 1
  rw [sN,← Complex.ofReal_mul,← sq,Real.sq_sqrt (by positivity)]
  push_cast; rfl
private theorem uniformExpr (p : Poly) : ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧
    ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ x y : ℝ, ‖expr p z x y‖ ≤ C*(weight x y)^k := by
  obtain ⟨C,k,hC,h⟩ := uniformGrowth p
  refine ⟨C,k,hC,fun z hz x y => ?_⟩
  rw [expr,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (exp_le hz _ _)).trans (h z hz x y)
private def dom (k : ℕ) (t : ℝ×ℝ) := weight t.1 t.2^k
private theorem domInt (k : ℕ) : Integrable (dom k) (γ.prod γ) := by
  have hi : Integrable (fun u : ℝ => (1+u^2)^k) γ := by
    convert polyInt ((1+(Polynomial.X : ℤ[X])^2)^k) using 1
    ext u; simp
  change Integrable (fun t : ℝ×ℝ => weight t.1 t.2^k) (γ.prod γ)
  simpa only [weight,mul_pow] using! hi.mul_prod hi
private theorem boundedCoeff (p : Poly) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ n : ℕ, ∀ z : ℂ, ‖z‖ ≤ 1 → ‖coeff p n z‖ ≤ B := by
  obtain ⟨C,k,hC,h⟩ := uniformExpr p
  let b (t : ℝ×ℝ) := C^2*dom (k*2) t
  let B := ∫ t, b t ∂γ.prod γ
  have b0 (t : ℝ×ℝ) : 0 ≤ b t := mul_nonneg (sq_nonneg _) (pow_nonneg (zero_le_one.trans (one_weight _ _)) _)
  have hB : 0 ≤ B := integral_nonneg b0
  refine ⟨B+1,by linarith,?_⟩
  intro n z hz
  have hB2 := gaussian_hermite_diagonal_bessel (fun t : ℝ×ℝ => expr p z t.1 t.2) (normLp p hz) {n}
  simp only [Finset.sum_singleton,Complex.ofReal_mul,← mul_assoc] at hB2
  change ‖coeff p n z‖^2 ≤ ∫ t : ℝ×ℝ, ‖expr p z t.1 t.2‖^2 ∂γ.prod γ at hB2
  have hb : ‖coeff p n z‖^2 ≤ B := hB2.trans (integral_mono
    ((memLp_two_iff_integrable_sq_norm (expr_ct _ _).aestronglyMeasurable).1 (normLp p hz))
    ((domInt (k*2)).const_mul (C^2)) (fun t => by
      simpa only [b,dom,mul_pow,← pow_mul] using pow_le_pow_left₀ (norm_nonneg _) (h z hz t.1 t.2) 2))
  nlinarith only [hb,sq_nonneg (‖coeff p n z‖-1),hB]
private theorem summableModes (p : Poly) : ∃ u : ℕ → ℝ, Summable u ∧
    ∀ n : ℕ, ∀ z : ℂ, ‖z‖ ≤ 1 → ‖(-z)^n*coeff p n z‖ ≤ u n := by
  obtain ⟨L,hL,h⟩ := boundedCoeff p
  obtain ⟨D,hD,hd⟩ := boundedCoeff (xy (xy p))
  let u : ℕ → ℝ := fun n => (9*(L+D))/((n:ℝ)+1)^2
  have hs := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  refine ⟨u,?_,?_⟩
  · simpa only [u,div_eq_mul_inv,one_mul,Nat.cast_add,Nat.cast_one] using hs.mul_left (9*(L+D))
  · intro n z hz
    rw [norm_mul,norm_pow,norm_neg]
    apply (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)).trans
    unfold u
    rw [le_div_iff₀ (by positivity)]
    cases n with
    | zero => simpa using (by nlinarith only [h 0 z hz,hD,hL] : ‖coeff p 0 z‖ ≤ 9*(L+D))
    | succ n =>
      cases n with
      | zero =>
        norm_num
        nlinarith only [h 1 z hz,hD,hL]
      | succ n =>
        have hb := hd n z hz
        rw [coeff_shift (xy p) n hz,coeff_shift p (n+1) hz,norm_mul,norm_mul] at hb
        have normc (i : ℕ) : ‖(i:ℂ)+1‖ = (i:ℝ)+1 := by
          rw [← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        rw [normc n,normc (n+1)] at hb
        simp only [Nat.cast_succ] at hb ⊢
        have n0 := Nat.cast_nonneg (α:=ℝ) n
        have hn : (((n:ℝ)+1+1)+1)^2 ≤ 9*((n:ℝ)+1)*(n+1+1) := by nlinarith only [sq_nonneg (n:ℝ),n0]
        have caseB := mul_le_mul_of_nonneg_left hn (norm_nonneg (coeff p (n+1+1) z))
        nlinarith only [hb,caseB,hL]

private theorem weightedHermInt (k n : ℕ) : Integrable (fun t : ℝ => (1+t^2)^k*‖H n t‖) γ := by
  let P : ℤ[X] := (1+Polynomial.X^2)^k*hermite n
  have hi := (polyInt P).abs.div_const (Real.sqrt (n.factorial:ℝ))
  apply hi.congr (ae_of_all _ fun t => ?_)
  simp only [P,H,QuadSDE.hermiteN,map_mul,map_pow,map_add,map_one,aeval_X,Complex.norm_real,Real.norm_eq_abs,
    abs_div,abs_mul,abs_of_nonneg (show 0 ≤ (1+t^2)^k by positivity),abs_of_nonneg (Real.sqrt_nonneg _)]
  ring
private theorem integrableDom (p : Poly) (n : ℕ) : ∃ b : ℝ×ℝ → ℝ, Integrable b (γ.prod γ) ∧
    ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ t : ℝ×ℝ, ‖A p z n n t.1 t.2‖ ≤ b t := by
  obtain ⟨C,k,hC,h⟩ := uniformExpr p
  let a (t : ℝ) := (1+t^2)^k*‖H n t‖
  refine ⟨fun t => C*(a t.1*a t.2),((weightedHermInt k n).mul_prod (weightedHermInt k n)).const_mul C,?_⟩
  intro z hz t
  simp only [A,norm_mul,a]
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h z hz t.1 t.2) (norm_nonneg (H n t.1))) (norm_nonneg (H n t.2))
  apply hb.trans_eq
  simp only [weight,mul_pow]; ring
private theorem coeffD (p : Poly) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (coeff p n) (coeff (dp dz p) n z) z := by
  let B := Metric.ball (0:ℂ) 1
  have hBs : B ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds (by simpa [B,Metric.mem_ball] using hz)
  have bnd (v : ℂ) (hv : v ∈ B) : ‖v‖ ≤ 1 := (by simpa [B,Metric.mem_ball] using hv : ‖v‖ < 1).le
  have hx : ∀ᶠ w in 𝓝 z, w ∈ B := hBs
  obtain ⟨b,hi,hb⟩ := integrableDom (dp dz p) n
  have hr := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w (t : ℝ×ℝ) => A p w n n t.1 t.2)
    (F' := fun w (t : ℝ×ℝ) => A (dp dz p) w n n t.1 t.2) (μ := γ.prod γ)
    hBs (hx.mono (fun w hw => (integrableA p (bnd w hw) n n).aestronglyMeasurable))
    (integrableA p hz.le n n) (integrableA (dp dz p) hz.le n n).aestronglyMeasurable
    (ae_of_all _ (fun t w hw => hb w (bnd w hw) t)) hi
    (ae_of_all _ (fun t w hw => ((exprZ p (diskU (bnd w hw)) t.1 t.2).mul_const (H n t.1)).mul_const (H n t.2)))
  exact hr.2
private theorem coeffC (p : Poly) (n : ℕ) :
    ContinuousOn (coeff p n) (Metric.closedBall (0:ℂ) 1) := by
  let B := Metric.closedBall (0:ℂ) 1
  have hB (z : ℂ) (hz : z ∈ B) : ‖z‖ ≤ 1 := by simpa [B,Metric.mem_closedBall] using hz
  obtain ⟨b,hi,hb⟩ := integrableDom p n
  apply continuousOn_of_dominated (F := fun z (t : ℝ×ℝ) => A p z n n t.1 t.2) (bound := b)
  · intro z hz; exact (integrableA p (hB z hz) n n).aestronglyMeasurable
  · intro z hz; exact ae_of_all _ (hb z (hB z hz))
  · exact hi
  · apply ae_of_all
    intro t z hz
    exact (((exprZ p (diskU (hB z hz)) t.1 t.2).mul_const (H n t.1)).mul_const (H n t.2)).continuousAt.continuousWithinAt
private def TP (p : Poly) (z : ℂ) := ∑' n : ℕ, (-z)^n*coeff p n z
private theorem TS (p : Poly) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => (-z)^n*coeff p n z) (TP p z) := by
  obtain ⟨u,hu,h⟩ := summableModes p
  exact ((Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => h n z hz) hu).of_norm).hasSum
private theorem singleD (p : Poly) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun w : ℂ => (-w)^n*coeff p n w) z :=
  (differentiableAt_id.neg.pow n).mul (coeffD p n hz).differentiableAt
private theorem Tdiff (p : Poly) {z : ℂ} (hz : ‖z‖ < 1) : DifferentiableAt ℂ (TP p) z := by
  obtain ⟨u,hu,h⟩ := summableModes p
  have hd := Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => (-w)^n*coeff p n w)
    hu (fun n w (hw : w ∈ Metric.ball (0:ℂ) 1) => (singleD p n (by simpa [Metric.mem_ball] using hw)).differentiableWithinAt)
    Metric.isOpen_ball (fun n w hw => h n w (by simpa [Metric.mem_ball] using hw : ‖w‖ < 1).le)
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball] using hz))
private theorem stepCoeff (p : Poly) (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    coeff (afterStep p) n z = z*(coeff (dp dz p) n z-coeff (xy p) n z) := by
  unfold coeff
  rw [← integral_sub (integrableA _ hz _ _) (integrableA _ hz _ _),← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [A,expr,afterStep,subP,negP,xy,ev,Z,con,id_eq]
  ring
private theorem raiseTrace (p : Poly) {z : ℂ} (hz : ‖z‖ < 1) :
    TP (afterStep p) z = z*deriv (TP p) z := by
  let f (n : ℕ) (w : ℂ) := (-w)^n*coeff p n w
  obtain ⟨u,hu,h⟩ := summableModes p
  have hder := Complex.hasSum_deriv_of_summable_norm (F := f) hu
    (fun n w (hw : w ∈ Metric.ball (0:ℂ) 1) => (singleD p n (by simpa [Metric.mem_ball] using hw)).differentiableWithinAt)
    Metric.isOpen_ball (fun n w hw => h n w (by simpa [Metric.mem_ball] using hw : ‖w‖ < 1).le)
    (show z ∈ Metric.ball 0 1 by simpa [Metric.mem_ball] using hz)
  have term (n : ℕ) : z*deriv (f n) z =
      z*((-z)^n*coeff (dp dz p) n z) + (n:ℂ)*(-z)^n*coeff p n z := by
    have hh := (((hasDerivAt_id z).neg.pow n).mul (coeffD p n hz)).deriv
    change deriv (f n) z = (n:ℂ)*(-z)^(n-1)*(-1)*coeff p n z+(-z)^n*coeff (dp dz p) n z at hh
    rw [hh]
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,pow_succ,Nat.cast_succ]; ring
  let b (n : ℕ) := (n:ℂ)*(-z)^n*coeff p n z
  have hs : HasSum b ((-z)*TP (xy p) z) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one,Finset.sum_singleton,b,Nat.cast_zero,zero_mul,sub_zero]
    apply ((TS (xy p) hz.le).mul_left (-z)).congr_fun
    intro n
    rw [coeff_shift _ _ hz.le,pow_succ,Nat.cast_succ]
    ring
  have g : HasSum (fun n => z*deriv (f n) z) (z*TP (dp dz p) z+(-z)*TP (xy p) z) :=
    (((TS (dp dz p) hz.le).mul_left z).add hs).congr_fun (fun n => term n)
  have e : z*deriv (TP p) z = z*TP (dp dz p) z+(-z)*TP (xy p) z := (hder.mul_left z).unique g
  rw [e]
  have htot := (((TS (dp dz p) hz.le).mul_left z).add ((TS (xy p) hz.le).mul_left (-z))).congr_fun
    (g := fun n => (-z)^n*coeff (afterStep p) n z) (fun n => by rw [stepCoeff p n hz.le]; ring)
  exact htot.tsum_eq

private theorem stepReal (p : Poly) {t : ℝ} (ht : |t| < 1) :
    TP (afterStep p) (t:ℂ) = (t:ℂ) * deriv (fun u : ℝ => TP p (u:ℂ)) t := by
  have hz : ‖(t:ℂ)‖ < 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using ht
  rw [raiseTrace p hz,(Tdiff p hz).hasDerivAt.comp_ofReal.deriv]

open Filter
private def rE (h : ℝ → ℝ) := fun t => t*deriv h t
private def cE (h : ℝ → ℂ) := fun t : ℝ => (t:ℂ)*deriv h t
private theorem rEA {h : ℝ → ℝ} (ha : AnalyticAt ℝ h 0) : AnalyticAt ℝ (rE h) 0 :=
  analyticAt_id.mul ha.deriv
private theorem liftE {h : ℝ → ℂ} {a : ℝ → ℝ} (ha : AnalyticAt ℝ a 0)
    (hh : h =ᶠ[𝓝 0] fun t : ℝ => Complex.ofReal (a t)) :
    cE h =ᶠ[𝓝 0] fun t : ℝ => Complex.ofReal (rE a t) := by
  filter_upwards [hh.deriv,ha.eventually_analyticAt] with t ht hs
  simp only [cE,rE,Complex.ofReal_mul]
  rw [ht,hs.differentiableAt.hasDerivAt.ofReal_comp.deriv]
private theorem realGerm :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (fun t : ℝ => CQBoundary.diskTrace (t:ℂ)) =ᶠ[𝓝 0]
      (fun t : ℝ => Complex.ofReal (t * deriv (fun u : ℝ => u * deriv (fun v : ℝ => v * deriv H v) u) t)) := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  have ha : AnalyticAt ℝ H 0 := CubicTaylor.corr_analytic _ _ _
  have near : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 := (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
  have coeffInt (p : Poly) {t : ℝ} (ht : |t| < 1) (n : ℕ) : coeff p n (t:ℂ) =
      ∫ x : ℝ, ∫ y : ℝ, expr p (t:ℂ) x y * Complex.ofReal (QuadSDE.hermiteN n x*QuadSDE.hermiteN n y) ∂γ ∂γ := by
    have hz : ‖(t:ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using ht.le
    unfold coeff
    rw [integral_prod _ (integrableA p hz n n)]
    simp only [A,KernelRegular.H,Complex.ofReal_mul,mul_assoc]
  have h1 : (fun t : ℝ => TP pOne (t:ℂ)) =ᶠ[𝓝 0] fun t => Complex.ofReal (rE H t) := by
    have h := cq_first_euler_gaussian_price
    filter_upwards [near,h] with t ht he
    change TP pOne (t:ℂ) = Complex.ofReal (t*deriv H t)
    rw [← he]
    apply tsum_congr
    intro n
    rw [coeffInt pOne ht n]
    simp only [phiOneExpr,γ]
  have hstep (p : Poly) : (fun t : ℝ => TP (afterStep p) (t:ℂ)) =ᶠ[𝓝 0]
      cE (fun t => TP p (t:ℂ)) := near.mono (fun t ht => stepReal p ht)
  have h2 := (hstep pOne).trans (liftE (rEA ha) h1)
  have h3 := (hstep (afterStep pOne)).trans (liftE (rEA (rEA ha)) h2)
  apply Filter.EventuallyEq.trans _ h3
  filter_upwards [near] with t ht
  have hz : ‖(t:ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using ht.le
  apply tsum_congr
  intro n
  rw [coeffInt (afterStep (afterStep pOne)) ht n]
  simp only [phiThreeExpr (diskU hz),pThree,γ]

end KernelRegular

open KernelRegular Filter
open scoped Topology
theorem solution :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (fun t : ℝ => CQBoundary.diskTrace (t:ℂ)) =ᶠ[𝓝 0]
      (fun t : ℝ => Complex.ofReal (t * deriv (fun u : ℝ => u * deriv (fun v : ℝ => v * deriv H v) u) t)) := realGerm
