-- Prove2me | solution 1 for NoHair.static_conformal_horizon_matching_forms
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:42:38.512931+00:00
-- url     : https://prove2.me/submissions/d2d6c893-83a3-4a1f-a88e-a23fbd76ece1

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

set_option maxHeartbeats 900000 in
theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ frontier Ω, ∀ s : ℝ, s = 1 ∨ s = -1 →
      let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := staticPositiveMetric (fun y => s*N y) h
      (∀ i j : Fin 3, k x i j = h x i j / 16) ∧
      staticLapseGradientSq N k x = (4*κ)^2 ∧
      ∀ v w : ADMPoint, fderiv ℝ N x v = 0 → fderiv ℝ N x w = 0 →
        (∑ i : Fin 3, ∑ j : Fin 3, staticSpatialHessian N k i j x * v i * w j) / (4*κ) =
          s*8*κ*(∑ i : Fin 3, ∑ j : Fin 3, k x i j * v i * w j) := by
  classical
  obtain ⟨κ,hκ,horizon⟩ := c.horizon
  refine ⟨κ,hκ,?_⟩
  intro x hx s _
  let k : X → Mat := staticPositiveMetric (fun y => s*N y) h
  let A := fun y : X => ((1+s*N y)/2)^4
  let n := fun i : I => pd i N x
  let r := fun a : I => staticRaisedGradient N h a x
  let B := (h x)⁻¹
  have wx := c.extendsAcross (frontier_subset_closure hx)
  have hp := c.positiveMetric x wx
  have h0 := (c.regularLevel x hx).1
  obtain ⟨hH,en,_⟩ := horizon x hx
  have energy : ∑ a : I, n a*r a = κ^2 := en
  have rval (a : I) : r a = ∑ l : I, B a l*n l := rfl
  have cn := c.smoothLapse.contDiffAt (c.openExtension.mem_nhds wx)
  have ch (i j : I) := (c.smoothMetric i j).contDiffAt (c.openExtension.mem_nhds wx)
  have dn := (cn.differentiableAt (by simp)).hasFDerivAt
  have dA := ((((dn.const_mul s).const_add 1).mul_const ((2:ℝ)⁻¹)).pow 4)
  have dA' : DifferentiableAt ℝ A x := by simpa only [A,div_eq_mul_inv] using dA.differentiableAt
  have A0 : A x = 1/16 := by norm_num [A,h0]
  have Ad (t : I) : pd t A x = s/4*n t := by
    have H := dA.fderiv
    change fderiv ℝ (fun y => ((1+s*N y)*(2:ℝ)⁻¹)^4) x = _ at H
    change fderiv ℝ A x (bvec t) = s/4 * fderiv ℝ N x (bvec t)
    simp only [A,div_eq_mul_inv,H,h0,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.zero_apply,smul_eq_mul,nsmul_eq_mul]
    ring
  have mat : k x = (1/16:ℝ) • h x := by
    ext i j
    change A x * h x i j = (1/16:ℝ)*h x i j
    rw [A0]
  have inv : (k x)⁻¹ = (16:ℝ) • B := by
    apply Matrix.inv_eq_right_inv
    have base : h x * B = 1 := Matrix.mul_nonsing_inv _ ((h x).isUnit_iff_isUnit_det.mp hp.isUnit)
    rw [mat,Matrix.smul_mul,Matrix.mul_smul,base,smul_smul]
    norm_num
  have kiv (i j : I) : (k x)⁻¹ i j = 16 * B i j := congrArg (fun m : Mat => m i j) inv
  have kd (t i j : I) : spatialADMPartial t (fun y => k y i j) x =
      s/4*n t*h x i j + (1/16)*spatialADMPartial t (fun y => h y i j) x := by
    change pd t (fun y => A y * h y i j) x = _
    rw [pd_mul (f:=A) (g:=fun y => h y i j) dA' ((ch i j).differentiableAt (by simp)) t,Ad,A0]
  have product (a j : I) : ∑ l : I, B a l * h x l j = (1:Mat) a j := by
    have bh : B*h x=1 := Matrix.nonsing_inv_mul _ ((h x).isUnit_iff_isUnit_det.mp hp.isUnit)
    exact congrArg (fun m : Mat => m a j) bh
  have connection (a i j : I) : spatialLeviCivita k x a i j = spatialLeviCivita h x a i j +
      2*s*((1:Mat) a j*n i + (1:Mat) a i*n j - r a*h x i j) := by
    rw [←product a i,←product a j,rval]
    simp only [spatialLeviCivita,kiv,kd,Fin.sum_univ_three,B]
    ring
  have ident (i : I) : ∑ a : I, (1:Mat) a i*n a = n i := by simp [Matrix.one_apply]
  have Hess (i j : I) : staticSpatialHessian N k i j x = 2*s*κ^2*h x i j - 4*s*n i*n j := calc
    _ = staticSpatialHessian N h i j x - 2*s*
          (n i*(∑ a : I, (1:Mat) a j*n a) + n j*(∑ a : I, (1:Mat) a i*n a) -
           h x i j*(∑ a : I, n a*r a)) := by
      simp only [staticSpatialHessian,connection,Fin.sum_univ_three,n,pd]
      ring
    _ = _ := by rw [ident,ident,energy,hH]; ring
  have kv (i j : I) : k x i j = h x i j/16 := by
    change A x*h x i j = _
    rw [A0]
    ring
  refine ⟨kv,?_,?_⟩
  · calc
      staticLapseGradientSq N k x = 16*(∑ a : I, n a * r a) := by
        simp only [staticLapseGradientSq,staticRaisedGradient,kiv,rval,n,pd,Fin.sum_univ_three]
        ring
      _ = _ := by rw [energy]; ring
  · intro v w tv tw
    have component (u : X) : ∑ i : I, n i*u i = fderiv ℝ N x u := by
      have H := congrArg (fun z : X => fderiv ℝ N x z) ((EuclideanSpace.basisFun I ℝ).sum_repr u)
      simpa only [map_sum,map_smul,EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_repr,smul_eq_mul,
        mul_comm,n,pd,spatialADMPartial] using H
    have vals := calc
      (∑ i : I, ∑ j : I, staticSpatialHessian N k i j x*v i*w j) =
        2*s*κ^2*(∑ i : I, ∑ j : I, h x i j*v i*w j) -
        4*s*(∑ i : I, n i*v i)*(∑ j : I, n j*w j) := by
          simp only [Hess,Fin.sum_univ_three]
          ring
      _ = 2*s*κ^2*(∑ i : I, ∑ j : I, h x i j*v i*w j) := by rw [component,component,tv,tw]; ring
    change (∑ i : I, ∑ j : I, staticSpatialHessian N k i j x*v i*w j)/(4*κ) =
      s*8*κ*(∑ i : I, ∑ j : I, k x i j * v i * w j)
    rw [vals]
    simp only [kv,Fin.sum_univ_three]
    field_simp [hκ.ne'] <;> ring
