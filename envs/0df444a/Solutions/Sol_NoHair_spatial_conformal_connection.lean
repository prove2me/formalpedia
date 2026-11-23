-- Prove2me | solution 1 for NoHair.spatial_conformal_connection
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:01:04.347527+00:00
-- url     : https://prove2.me/submissions/1399cec5-d4f5-4c43-ad22-2cad031c1ea9

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

private noncomputable abbrev fourth (u : X → ℝ) (h : X → Mat) (y : X) : Mat :=
  (u y ^ 4) • h y

private def kr (a i : I) : ℝ := if a=i then 1 else 0

theorem solution (u : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hu : ContDiffOn ℝ ∞ u W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (x : ADMPoint) (hx : x ∈ W) (hn : u x ≠ 0) :
    let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := fun y => (u y ^ 4) • h y
    (k x)⁻¹ = ((u x ^ 4)⁻¹) • (h x)⁻¹ ∧
    ∀ a i j : Fin 3, spatialLeviCivita k x a i j = spatialLeviCivita h x a i j +
      (if a=i then 1 else 0) * (2/u x * spatialADMPartial j u x) +
      (if a=j then 1 else 0) * (2/u x * spatialADMPartial i u x) -
      h x i j * (2/u x * staticRaisedGradient u h a x) := by
  classical
  let k := fourth u h
  let B := (h x)⁻¹
  have detU := (h x).isUnit_iff_isUnit_det.mp (hp x hx).isUnit
  have inv : (k x)⁻¹ = ((u x ^ 4)⁻¹) • B := by
    apply Matrix.inv_eq_right_inv
    change ((u x ^ 4) • h x) * ((u x ^ 4)⁻¹ • B) = 1
    have hb : h x * B = 1 := Matrix.mul_nonsing_inv _ detU
    rw [Matrix.smul_mul,Matrix.mul_smul,hb,smul_smul]
    simp [hn]
  refine ⟨inv,?_⟩
  intro a i j
  have cn := hu.contDiffAt (hw.mem_nhds hx)
  have ch (i j : I) := (hh i j).contDiffAt (hw.mem_nhds hx)
  have z4 := ((cn.differentiableAt (by simp)).hasFDerivAt.pow 4)
  have powD (t : I) : pd t (fun y => u y ^ 4) x = 4*u x^3*pd t u x := by
    unfold pd spatialADMPartial
    rw [z4.fderiv]
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,nsmul_eq_mul]
    norm_num
  have dk (t i j : I) : spatialADMPartial t (fun y => k y i j) x =
      4*u x^3*pd t u x*h x i j + u x^4*pd t (fun y => h y i j) x := by
    change pd t (fun y => u y^4*h y i j) x = _
    rw [pd_mul (f:=fun y => u y^4) (g:=fun y => h y i j) z4.differentiableAt
      ((ch i j).differentiableAt (by simp)) t,powD]
  have ib (r l : I) : (k x)⁻¹ r l = (u x ^ 4)⁻¹ * B r l := congrArg (fun m : Mat => m r l) inv
  have product (t : I) : ∑ l : I, B a l*h x l t = kr a t := by
    have bh : B*h x=1 := Matrix.nonsing_inv_mul _ detU
    rw [show kr a t = (1:Mat) a t by simp only [kr,Matrix.one_apply]]
    exact congrArg (fun m : Mat => m a t) bh
  change spatialLeviCivita k x a i j = spatialLeviCivita h x a i j + kr a i * _ + kr a j * _ - _
  rw [←product i,←product j]
  simp only [spatialLeviCivita,staticRaisedGradient,ib,dk,Fin.sum_univ_three,B,pd]
  field_simp [hn] <;> ring
