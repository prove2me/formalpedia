-- Prove2me | solution 2 for NoHair.static_minus_point_chart_from_hansen_data
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:37:31.349201+00:00
-- url     : https://prove2.me/submissions/efa55fc6-b1c5-4958-9c43-5a7107d484d8

import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric
open NoHair Set Filter Metric
open scoped Topology ContDiff
private abbrev X := ADMPoint
private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
private lemma quad_scale (h : X → Mat) (k : X → ℝ) (x v : X) :
    staticChartQuadratic (fun y => k y • h y) x v=k x*staticChartQuadratic h x v := by
  simp only [staticChartQuadratic,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem solution (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ∃ (a : StaticMinusPointChart Ω N (fun x : ADMPoint => (((1+N x)^4)/(N x)^2) • h x)) (b : ADMPoint → ℝ),
      b 0 = 0 ∧ ContDiffOn ℝ ∞ b (ball 0 a.radius) ∧ (∀ y ∈ ball 0 a.radius, b y < 1) ∧
      ∀ y ∈ a.change.source, 0 < N (a.change y) ∧
        b y = ((1-N (a.change y))/(1+N (a.change y)))^2) :
    Nonempty (StaticMinusPointChart Ω N h) := by
  obtain ⟨a,b,_,sb,ub,matchb⟩:=hg
  let f:=fun y : X => (1-b y)^2/16
  have sf : ContDiffOn ℝ ∞ f (ball 0 a.radius) :=
    ((contDiffOn_const.sub sb).pow 2).div_const 16
  have pf {y : X} (hy : y∈ball 0 a.radius) : 0<f y :=
    div_pos (sq_pos_of_pos (sub_pos.mpr (ub y hy))) (by norm_num)
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
    pullsBack := ?_ }⟩
  intro y hy v
  let z:=a.change y
  have pn : 0<N z := (matchb y hy).1
  have hp : 1+N z≠0 := by linarith
  have eq : f y * ((1+N z)^4/(N z)^2)=1 := by
    dsimp only [f]
    rw [(matchb y hy).2]
    change (1-((1-N z)/(1+N z))^2)^2/16*((1+N z)^4/(N z)^2)=1
    field_simp [hp,pn.ne'] <;> ring
  rw [quad_scale,a.pullsBack y hy v]
  let g : X → Mat :=staticPositiveMetric (fun x => -N x) h
  let K:=fun x => (1+N x)^4/(N x)^2
  have hk : staticPositiveMetric (fun x => -N x) (fun x => K x • h x)=fun (x:X) => (K x • g x : Mat) := by
    funext x i j
    change ((1+ -N x)/2)^4*(K x*h x i j)=K x*(((1+ -N x)/2)^4*h x i j)
    ring
  change f y*staticChartQuadratic (staticPositiveMetric (fun x => -N x) (fun x => K x • h x)) z _=_
  rw [hk,quad_scale g K,←mul_assoc,show f y*K z=1 from eq,one_mul]
