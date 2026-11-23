-- Prove2me | solution 1 for NoHair.diffeomorphism_of_bijective_radial_scale
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:25:03.371751+00:00
-- url     : https://prove2.me/submissions/4e229141-3ce2-4466-a690-6ae86a65cb51

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
open NoHair Set Filter Metric
open scoped Topology ContDiff
private abbrev X := ADMPoint

theorem solution (u : ADMPoint → ℝ) (S T : Set ADMPoint) (hS : IsOpen S) (hT : IsOpen T)
    (bij : BijOn (fun x : ADMPoint => u x • x) S T)
    (reg : ∀ x ∈ S, ContDiffAt ℝ ∞ u x ∧ u x ≠ 0 ∧ u x + fderiv ℝ u x x ≠ 0) :
    ∃ e : OpenPartialHomeomorph ADMPoint ADMPoint, e.source = S ∧ e.target = T ∧
      (∀ x ∈ S, e x = u x • x) ∧ ContDiffOn ℝ ∞ e S ∧ ContDiffOn ℝ ∞ e.symm T := by
  classical
  let F:=fun x : X => u x • x
  let pe:=bij.toPartialEquiv F S T
  have sm {x : X} (hx : x∈S) : ContDiffAt ℝ ∞ F x := (reg x hx).1.smul contDiffAt_id
  have inv {y : X} (hy : y∈T) : ContDiffAt ℝ ∞ pe.symm y := by
    let x:=pe.symm y
    have hx : x∈S := pe.map_target hy
    have eqy : F x=y := pe.right_inv hy
    obtain ⟨du,un,dr⟩:=reg x hx
    let L:=fderiv ℝ F x
    let l:=fderiv ℝ u x
    have hL (v : X) : L v=u x • v+l v • x := by
      dsimp only [L,F,l]
      rw [fderiv_fun_smul (f:=fun z : X => z) (du.differentiableAt (by simp)) (differentiableAt_id (𝕜:=ℝ) (x:=x))]
      simp
    have ker : L.ker=⊥ := by
      apply LinearMap.ker_eq_bot'.2
      intro v hv
      change L v=0 at hv
      rw [hL] at hv
      have eq:=congrArg l hv
      simp only [map_add,map_smul,smul_eq_mul,map_zero] at eq
      have hprod : (u x+l x)*l v=0 := by linarith only [eq,show (u x+l x)*l v=u x*l v+l v*l x by ring]
      have lv:=(mul_eq_zero.mp hprod).resolve_left dr
      rw [lv,zero_smul,add_zero] at hv
      exact (smul_eq_zero.mp hv).resolve_left un
    have sur : L.range=⊤ := LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp ker))
    let A : X ≃L[ℝ] X := ContinuousLinearEquiv.ofBijective L ker sur
    have dF : HasFDerivAt F (A : X →L[ℝ] X) x := by
      rw [show (A : X →L[ℝ] X)=L from ContinuousLinearEquiv.coe_ofBijective L ker sur]
      exact ((sm hx).differentiableAt (by simp : (∞:ℕ∞ω)≠0)).hasFDerivAt
    let q:=(sm hx).toOpenPartialHomeomorph F dF (by simp)
    have qf : (q : X → X)=F := rfl
    have qx : x∈q.source := (sm hx).mem_toOpenPartialHomeomorph_source dF (by simp)
    have qy : y∈q.target := eqy ▸ q.map_source qx
    have qy' : q.symm y=x := eqy ▸ q.left_inv qx
    have qs : ContDiffAt ℝ ∞ q.symm y := by
      rw [←eqy]
      exact (sm hx).to_localInverse dF (by simp)
    apply qs.congr_of_eventuallyEq
    have localS : ∀ᶠ z in 𝓝 y,q.symm z∈S := qs.continuousAt.tendsto (hS.mem_nhds (qy'.symm ▸ hx))
    filter_upwards [hT.mem_nhds hy,q.open_target.mem_nhds qy,localS] with z hzt hzq hzs
    apply bij.injOn (pe.map_target hzt) hzs
    exact (pe.right_inv hzt).trans (q.right_inv hzq).symm
  let e : OpenPartialHomeomorph X X := {
    toPartialEquiv:=pe
    open_source:=hS
    open_target:=hT
    continuousOn_toFun:=fun x hx => (sm hx).continuousAt.continuousWithinAt
    continuousOn_invFun:=fun y hy => (inv hy).continuousAt.continuousWithinAt }
  exact ⟨e,rfl,rfl,fun _ _ => rfl,fun _ hx => (sm hx).contDiffWithinAt,fun _ hy => (inv hy).contDiffWithinAt⟩
