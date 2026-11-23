-- Prove2me | solution 1 for NoHair.spatial_laplacian_in_divergence_form
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:34:56.918951+00:00
-- url     : https://prove2.me/submissions/68f48ea7-b2c3-43dd-b8d6-1a8932773d73

import Theorems.Thm_NoHair_static_lapse_gradient_covariant_derivative
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

private lemma sm_pd {f : X → ℝ} {x : X} (c : ContDiffAt ℝ ∞ f x) (i : I) :
    ContDiffAt ℝ ∞ (pd i f) x :=
  (c.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

private lemma sm_inv {h : X → Mat} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (a b : I) :
    ContDiffAt ℝ ∞ (fun y => (h y)⁻¹ a b) x := by
  classical
  have detS {ι : Type} [Fintype ι] [DecidableEq ι] (G : X → Matrix ι ι ℝ)
      (cG : ∀ k m, ContDiffAt ℝ ∞ (fun y => G y k m) x) :
      ContDiffAt ℝ ∞ (fun y => (G y).det) x := by
    simp_rw [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    have pr (t : Finset ι) : ContDiffAt ℝ ∞ (fun y => ∏ j ∈ t, G y (σ j) j) x := by
      induction t using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty] using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : X => (1:ℝ)) x)
      | @insert a t ha ih =>
        simp only [Finset.prod_insert ha]
        exact (cG _ _).mul ih
    exact contDiffAt_const.mul (pr Finset.univ)
  have det0 := ((h x).isUnit_iff_isUnit_det.mp hp.isUnit).ne_zero
  have adj : ContDiffAt ℝ ∞ (fun y => (h y).adjugate a b) x := by
    simp_rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    exact contDiffAt_const.mul (detS (ι:=Fin 2) (fun y => (h y).submatrix b.succAbove a.succAbove)
      (fun k m => hc _ _))
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact ((detS (ι:=I) h hc).inv det0).mul adj

private lemma sm_ch {h : X → Mat} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (a i j : I) :
    ContDiffAt ℝ ∞ (fun y => spatialLeviCivita h y a i j) x :=
  contDiffAt_const.mul (ContDiffAt.sum fun l _ => (sm_inv hp hc a l).mul
    (((sm_pd (hc l j) i).add (sm_pd (hc l i) j)).sub (sm_pd (hc i j) l)))

private lemma sm_grad {h : X → Mat} {N : X → ℝ} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (cn : ContDiffAt ℝ ∞ N x) (a : I) :
    ContDiffAt ℝ ∞ (staticRaisedGradient N h a) x :=
  ContDiffAt.sum fun j _ => (sm_inv hp hc a j).mul (sm_pd cn j)

private lemma sym_h {h : X → Mat} {W : Set X} (ow : IsOpen W)
    (hp : ∀ y ∈ W, (h y).PosDef) {x : X} (hx : x ∈ W) (i j k : I) :
    pd i (fun y => h y j k) x = pd i (fun y => h y k j) x := by
  have ev : (fun y => h y j k) =ᶠ[𝓝 x] (fun y => h y k j) := (show ∀ᶠ y in 𝓝 x, y ∈ W from ow.mem_nhds hx).mono
    (fun y hy => by simpa only [star_trivial] using (hp y hy).isHermitian.apply k j)
  exact congrArg (fun L : X →L[ℝ] ℝ => L (bvec i)) ev.fderiv_eq

private lemma pd_sum {f : I → X → ℝ} {x : X} (df : ∀ j, DifferentiableAt ℝ (f j) x) (i : I) :
    pd i (fun y => ∑ j, f j y) x = ∑ j, pd i (f j) x := by
  unfold pd spatialADMPartial
  rw [fderiv_fun_sum (fun j _ => df j)]
  simp

private lemma pd_mul {f g : X → ℝ} {x : X} (df : DifferentiableAt ℝ f x) (dg : DifferentiableAt ℝ g x) (i : I) :
    pd i (fun y => f y*g y) x = pd i f x*g x + f x*pd i g x := by
  have v := (df.hasFDerivAt.mul dg.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y*g y) x = _ at v
  unfold pd spatialADMPartial
  rw [v]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

private lemma dcmul {f : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : I) :
    pd i (fun y => c*f y) x=c*pd i f x := by
  unfold pd spatialADMPartial
  rw [(hf.hasFDerivAt.const_mul c).fderiv]; rfl

private lemma determinant_at_identity (k : X → Mat) (x : X) (atx : k x=1)
    (c : ∀ i j, DifferentiableAt ℝ (fun y => k y i j) x) :
    DifferentiableAt ℝ (fun y => (k y).det) x ∧
    ∀ i : I, pd i (fun y => (k y).det) x = ∑ a : I, pd i (fun y => k y a a) x := by
  have triple (a b c' d e f' : I) := (((c a b).hasFDerivAt.mul (c c' d).hasFDerivAt).mul (c e f').hasFDerivAt)
  have H := (((((triple 0 0 1 1 2 2).sub (triple 0 0 1 2 2 1)).sub (triple 0 1 1 0 2 2)).add
    (triple 0 1 1 2 2 0)).add (triple 0 2 1 0 2 1)).sub (triple 0 2 1 1 2 0)
  have K := H.congr_of_eventuallyEq (f₁:=fun y => (k y).det) (Filter.Eventually.of_forall fun y => Matrix.det_fin_three (k y))
  refine ⟨K.differentiableAt,?_⟩
  intro i
  change fderiv ℝ (fun y => (k y).det) x (bvec i) = _
  rw [K.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,
    smul_eq_mul,Pi.mul_apply,atx,Matrix.one_apply,Fin.sum_univ_three,pd,spatialADMPartial,bvec]
  norm_num [atx,Matrix.one_apply,show (0:I) ≠ 1 by decide,show (0:I) ≠ 2 by decide,
    show (1:I) ≠ 0 by decide,show (1:I) ≠ 2 by decide,show (2:I) ≠ 0 by decide,show (2:I) ≠ 1 by decide] <;> ring

set_option maxHeartbeats 650000 in
theorem solution (f : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef) (x : ADMPoint) (hx : x∈W) :
    (∑ i : Fin 3, spatialADMPartial i (fun y => Real.sqrt (h y).det * staticRaisedGradient f h i y) x) =
      Real.sqrt (h x).det * (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian f h i j x) := by
  classical
  let B := (h x)⁻¹
  let K := fun y => B*h y
  let vol := fun y => Real.sqrt (h y).det
  let V := staticRaisedGradient f h
  have px := hp x hx
  have detU := (h x).isUnit_iff_isUnit_det.mp px.isUnit
  have ch (i j : I) := (hh i j).contDiffAt (hw.mem_nhds hx)
  have du := hf.contDiffAt (hw.mem_nhds hx)
  have kval : K x = 1 := Matrix.nonsing_inv_mul _ detU
  have ent (a b : I) : (fun y => K y a b) = fun y => ∑ l : I, B a l * h y l b := by funext y; rfl
  have ck (a b : I) : DifferentiableAt ℝ (fun y => K y a b) x := by
    rw [ent]; exact (ContDiffAt.sum (n:=∞) fun l _ => contDiffAt_const.mul (ch l b)).differentiableAt (by simp)
  have normal := determinant_at_identity K x kval ck
  have factor : (fun y => (h y).det) = fun y => (h x).det*(K y).det := by
    funext y
    have base : h x * B = 1 := Matrix.mul_nonsing_inv _ detU
    dsimp only [K]
    rw [←Matrix.det_mul,←Matrix.mul_assoc,base,Matrix.one_mul]
  have cd : DifferentiableAt ℝ (fun y => (h y).det) x := by rw [factor]; exact normal.1.const_mul _
  have cv : DifferentiableAt ℝ vol x := ((Real.hasDerivAt_sqrt px.det_pos.ne').comp_hasFDerivAt x cd.hasFDerivAt).differentiableAt
  have detD (i : I) : pd i (fun y => (h y).det) x = (h x).det *
      (∑ a : I, ∑ l : I, B a l*pd i (fun y => h y l a) x) := by
    rw [factor,dcmul (f:=fun y => (K y).det) normal.1,normal.2]
    apply congrArg (fun v => (h x).det*v)
    apply Finset.sum_congr rfl
    intro a _
    rw [ent,pd_sum (f:=fun l y => B a l*h y l a)
      (fun l => ((ch l a).differentiableAt (by simp)).const_mul _)]
    exact Finset.sum_congr rfl fun l _ => dcmul (f:=fun y => h y l a) ((ch l a).differentiableAt (by simp)) _ i
  have Bs (a l : I) : B a l=B l a := by simpa only [star_trivial] using px.inv.isHermitian.apply l a
  have gamma (i : I) : 2*(∑ a : I, spatialLeviCivita h x a a i) =
      ∑ a : I, ∑ l : I, B a l*pd i (fun y => h y l a) x := by
    change 2*(∑ a : I, (1/2:ℝ)*(∑ l : I, B a l*
      (pd a (fun y => h y l i) x + pd i (fun y => h y l a) x - pd l (fun y => h y a i) x)))=_
    simp only [Fin.sum_univ_three,Bs]; ring
  have dvol (i : I) : pd i vol x=vol x*(∑ a : I, spatialLeviCivita h x a a i) := by
    have ev : (fun y => vol y*vol y) =ᶠ[𝓝 x] (fun y => (h y).det) :=
      (show ∀ᶠ y in 𝓝 x, y∈W from hw.mem_nhds hx).mono fun y wy =>
        Real.mul_self_sqrt (hp y wy).det_pos.le
    have eq := congrArg (fun L : X →L[ℝ] ℝ => L (bvec i)) ev.fderiv_eq
    change pd i (fun y => vol y*vol y) x = pd i (fun y => (h y).det) x at eq
    rw [pd_mul (f:=vol) (g:=vol) cv cv i,detD,←gamma] at eq
    have sq : vol x*vol x=(h x).det := Real.mul_self_sqrt px.det_pos.le
    have vn : vol x ≠ 0 := (Real.sqrt_pos.mpr px.det_pos).ne'
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) vn)
    rw [←sq] at eq
    linear_combination eq
  have row (i : I) : spatialADMPartial i (fun y => vol y*V i y) x =
      (vol x*(∑ a : I, spatialLeviCivita h x a a i))*V i x + vol x*pd i (V i) x := by
    change pd i (fun y => vol y*V i y) x=_
    rw [pd_mul (f:=vol) (g:=V i) cv ((sm_grad px ch du i).differentiableAt (by simp)) i,dvol]
  have cov (i : I) := (static_lapse_gradient_covariant_derivative f h W hw hf hh hp x hx i).1 i
  change (∑ i : I, spatialADMPartial i (fun y => vol y*V i y) x)=vol x*_
  simp_rw [row,←cov]
  simp only [Fin.sum_univ_three,V,pd]
  ring
