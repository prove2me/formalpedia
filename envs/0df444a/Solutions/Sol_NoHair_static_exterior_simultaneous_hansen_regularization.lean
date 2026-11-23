-- Prove2me | solution 1 for NoHair.static_exterior_simultaneous_hansen_regularization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:47:33.170801+00:00
-- url     : https://prove2.me/submissions/21b7980b-3e59-4241-879f-2a72890bf1af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_exterior_metric_falloff_gives_weighted_sobolev_bounds
import Theorems.Thm_NoHair_static_vacuum_weighted_end_analytic_compactification
import Definitions.Def_NoHair_staticInvertedEndMetric
open NoHair Set Filter Metric MeasureTheory
open scoped Topology ContDiff
private abbrev X := ADMPoint
private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
private lemma quad_scale (h : X → Mat) (k : X → ℝ) (x v : X) :
    staticChartQuadratic (fun y => k y • h y) x v=k x*staticChartQuadratic h x v := by
  simp only [staticChartQuadratic,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem solution (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (R μ : ℝ) (hR : 0 < R) (hm : 0<μ)
    (inside : ∀ x : ADMPoint, R<‖x‖ → x∈Ω) (mono : HasStaticLapseMonopole N μ)
    (positive : ∀ x : ADMPoint, R<‖x‖ → 0<N x ∧ N x<1 ∧ (h x).PosDef)
    (smooth : ∀ x : ADMPoint, R<‖x‖ → ContDiffAt ℝ ∞ N x ∧ ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (falloff : ∀ k : ℕ, ∃ L C : ℝ, 0<L ∧ 0<C ∧ ∀ x : ADMPoint, L<‖x‖ →
      ‖iteratedFDeriv ℝ k (fun y => N y-1) x‖ ≤ C/‖x‖^(k+1) ∧
      ∀ i j, ‖iteratedFDeriv ℝ k (fun y => h y i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j) x‖ ≤ C/‖x‖^(k+1))
    (equations : ∀ x : ADMPoint, R<‖x‖ →
      (∀ i j : Fin 3, staticSpatialHessian N h i j x = N x * spatialRicciTensor h x i j) ∧
      (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian N h i j x) = 0)
    (radial : ∃ (δ : ℝ) (e : OpenPartialHomeomorph ADMPoint ADMPoint), 0 < δ ∧
      e.source = ball 0 δ ∩ ({0} : Set ADMPoint)ᶜ ∧ e.target ⊆ Ω ∧
      (∃ R : ℝ, ∀ x : ADMPoint, R < ‖x‖ → x ∈ e.target) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      Tendsto (fun y : ADMPoint => ‖e y‖) (𝓝[≠] 0) atTop ∧
      Tendsto (fun x : ADMPoint => e.symm x) (cocompact ADMPoint) (𝓝 0) ∧
      ∀ y ∈ e.source, (1-N (e y))/(1+N (e y)) = ‖y‖) :
    ∃ (a : StaticMinusPointChart Ω N (fun x : ADMPoint => (((1+N x)^4)/(N x)^2) • h x)) (b : ADMPoint → ℝ),
      b 0 = 0 ∧ ContDiffOn ℝ ∞ b (ball 0 a.radius) ∧ (∀ y ∈ ball 0 a.radius, b y < 1) ∧
      ∀ y ∈ a.change.source, 0 < N (a.change y) ∧
        b y = ((1-N (a.change y))/(1+N (a.change y)))^2 := by
  obtain ⟨B,hB,weight⟩:=exterior_metric_falloff_gives_weighted_sobolev_bounds h R 3
    (fun x hx => (smooth x hx).2) (fun k => by
      obtain ⟨L,C,lp,cp,decay⟩:=falloff k
      exact ⟨L,C,lp,cp,fun x hx => (decay x hx).2⟩)
  have bigger := (le_max_left R 1).trans hB
  obtain ⟨a,b,b0,ab,_,ub,matchb⟩ := static_vacuum_weighted_end_analytic_compactification Ω N h B μ
    (hR.trans_le bigger) hm (fun x hx => inside x (bigger.trans_lt hx)) mono
    (fun x hx => positive x (bigger.trans_lt hx)) (fun x hx => smooth x (bigger.trans_lt hx)) weight
    (fun x hx => equations x (bigger.trans_lt hx))
  have sb : ContDiffOn ℝ ∞ b (ball 0 a.radius) := ab.contDiffOn_of_completeSpace
  let f:=fun y : X => 16/(1-b y)^2
  have nz {y:X} (hy : y∈ball 0 a.radius) : 0<(1-b y)^2 := sq_pos_of_pos (sub_pos.mpr (ub y hy))
  have sf : ContDiffOn ℝ ∞ f (ball 0 a.radius) :=
    contDiffOn_const.div ((contDiffOn_const.sub sb).pow 2) (fun y hy => (nz hy).ne')
  have pf {y:X} (hy : y∈ball 0 a.radius) : 0<f y := div_pos (by norm_num) (nz hy)
  let K:=fun x => (1+N x)^4/(N x)^2
  let g : X → Mat :=staticPositiveMetric (fun x => -N x) h
  have hk : staticPositiveMetric (fun x => -N x) (fun x => K x • h x)=fun (x:X) => (K x • g x : Mat) := by
    funext x i j
    change ((1+ -N x)/2)^4*(K x*h x i j)=K x*(((1+ -N x)/2)^4*h x i j)
    ring
  refine ⟨{
    radius := a.radius
    positive := a.positive
    change := a.change
    source := a.source
    inside := a.inside
    smoothChange := a.smoothChange
    smoothInverse := a.smoothInverse
    tendsOut := a.tendsOut
    tendsIn := a.tendsIn
    coversInfinity := a.coversInfinity
    coeff := fun y => f y • a.coeff y
    smooth := fun i j => sf.mul (a.smooth i j)
    definite := fun y hy => (a.definite y hy).smul (pf hy)
    pullsBack := ?_ },b,b0,sb,ub,matchb⟩
  intro y hy v
  let z:=a.change y
  have pn : 0<N z := (matchb y hy).1
  have hp : 1+N z≠0 := by linarith
  have den : 1-((1-N z)/(1+N z))^2=4*N z/(1+N z)^2 := by field_simp [hp] <;> ring
  have eq : f y=K z := by
    dsimp only [f]
    rw [(matchb y hy).2]
    change 16/(1-((1-N z)/(1+N z))^2)^2=(1+N z)^4/(N z)^2
    rw [den]
    field_simp [hp,pn.ne'] <;> ring
  rw [quad_scale,a.pullsBack y hy v]
  change f y*staticChartQuadratic g z _=staticChartQuadratic (staticPositiveMetric (fun x => -N x) (fun x => K x • h x)) z _
  rw [hk,quad_scale g K,eq]
