-- Prove2me | solution 1 for NoHair.spatial_laplacian_nonpositive_at_maximum
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:18:58.210058+00:00
-- url     : https://prove2.me/submissions/c1f50f61-ee30-40a1-adc0-0da5d3263bf2

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

open scoped Matrix

private abbrev X := ADMPoint
private abbrev I := Fin 3
private abbrev Mat := Matrix I I ℝ
private noncomputable abbrev pd := spatialADMPartial
private noncomputable abbrev bvec (i : I) : X := EuclideanSpace.single i 1

open scoped MatrixOrder

private lemma scalar_second_at_max {g : ℝ → ℝ} {t : ℝ} (hm : IsLocalMax g t) (hc : ContinuousAt g t) :
    deriv (deriv g) t ≤ 0 := by
  by_contra! h
  have mn := isLocalMin_of_deriv_deriv_pos h hm.deriv_eq_zero hc
  have eq : g =ᶠ[𝓝 t] (fun _ => g t) :=
    (hm.and mn).mono fun y hy => le_antisymm hy.1 hy.2
  have z := eq.deriv.deriv_eq
  simp at z
  linarith

theorem solution (W : Set ADMPoint) (f : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hw : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) 
    (x : ADMPoint) (hx : x∈W) (hp : (h x).PosDef) (hm : IsLocalMax f x) :
    (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian f h i j x) ≤ 0 := by
  classical
  let A := fderiv ℝ (fderiv ℝ f) x
  have cf := hf.contDiffAt (hw.mem_nhds hx)
  have df := (cf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have eval (v w : X) : fderiv ℝ (fun y => fderiv ℝ f y w) x v = A v w := by
    rw [fderiv_clm_apply (u:=fun _ : X => w) df (differentiableAt_const w)]
    simp [A]
  have neg (v : X) : A v v ≤ 0 := by
    let line := fun t : ℝ => x+t • v
    let g := f ∘ line
    have line0 : line 0=x := by simp [line]
    have ld (t : ℝ) : HasDerivAt line v t := by
      simpa [line] using (((hasDerivAt_id t).smul_const v).const_add x)
    have cw : ContinuousAt line 0 := (ld 0).continuousAt
    have mx : IsLocalMax g 0 := (show IsLocalMax f (line 0) by rwa [line0]).comp_continuous cw
    have ct : ContinuousAt g 0 := (show ContinuousAt f (line 0) by simpa only [line0] using cf.continuousAt).comp cw
    have nW : ∀ᶠ t in 𝓝 0, line t∈W := cw (hw.mem_nhds (line0 ▸ hx))
    have der : deriv g =ᶠ[𝓝 0] (fun t => fderiv ℝ f (line t) v) := nW.mono fun t ht =>
      (((hf.contDiffAt (hw.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (ld t)).deriv
    have cv := ((cf.fderiv_right (m:=∞) (by simp)).clm_apply (contDiffAt_const (c:=v))).differentiableAt (by simp)
    have d2 := ((show DifferentiableAt ℝ (fun y => fderiv ℝ f y v) (line 0) by rwa [line0]).hasFDerivAt.comp_hasDerivAt 0 (ld 0)).deriv
    change deriv (fun t => fderiv ℝ f (line t) v) 0 = _ at d2
    rw [line0,eval] at d2
    simpa only [der.deriv_eq,d2] using scalar_second_at_max mx ct
  have hess (i j : I) : staticSpatialHessian f h i j x = A (bvec i) (bvec j) := by
    have zero (k : I) : spatialADMPartial k f x=0 := by simp [spatialADMPartial,hm.fderiv_eq_zero]
    simp only [staticSpatialHessian,zero,mul_zero,Finset.sum_const_zero,sub_zero]
    exact eval _ _
  obtain ⟨C,hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp.inv.posSemidef.nonneg
  let v := fun k : I => ∑ i : I, C k i • bvec i
  have row (k : I) : A (v k) (v k) = ∑ i : I, ∑ j : I, C k i * C k j * A (bvec i) (bvec j) := by
    simp only [v,Fin.sum_univ_three,map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have ent (i j : I) : (h x)⁻¹ i j=∑ k : I, C k i*C k j := by
    have e := congrArg (fun m : Mat => m i j) hC
    simpa only [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial] using e
  calc
    _ = ∑ k : I, A (v k) (v k) := by
      simp only [hess,ent,row,Fin.sum_univ_three]; ring
    _ ≤ 0 := Finset.sum_nonpos fun k _ => neg (v k)
