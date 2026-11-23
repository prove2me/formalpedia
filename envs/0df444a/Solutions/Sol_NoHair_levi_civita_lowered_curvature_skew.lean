-- Prove2me | solution 1 for NoHair.levi_civita_lowered_curvature_skew
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:55:23.813566+00:00
-- url     : https://prove2.me/submissions/4f6bb020-e126-4eeb-9f38-c38b792177ca

import Definitions.Def_NoHair_spatialRiemannCurvature

open NoHair Set Filter Bundle
open scoped Topology ContDiff Manifold

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

private def con (h : X → Mat) (i : I) (x : X) : Mat := fun a b => spatialLeviCivita h x a i b
private def dm (i : I) (f : X → Mat) (x : X) : Mat := fun a b => pd i (fun y => f y a b) x
private abbrev sm (f : X → Mat) (x : X) := ∀ a b, ContDiffAt ℝ ∞ (fun y => f y a b) x

private lemma metric_id {h : X → Mat} {W : Set X} (op : IsOpen W)
    (pos : ∀ y∈W, (h y).PosDef) {x : X} (hx : x∈W) (i : I) :
    dm i h x = (con h i x)ᵀ*h x + h x*con h i x := by
  let M := h x
  let B := (h x)⁻¹
  let dh := fun t a b => pd t (fun y => h y a b) x
  let G := fun a l => spatialLeviCivita h x a i l
  have detU := (h x).isUnit_iff_isUnit_det.mp (pos x hx).isUnit
  have hb : M*B=1 := Matrix.mul_nonsing_inv _ detU
  have connection_lower (a l : I) : ∑ m : I, M a m * G m l =
      (dh i a l + dh l a i - dh a i l)/2 := by
    let t := fun k => (dh i k l + dh l k i - dh k i l)/2
    have chr (m : I) : G m l = (B *ᵥ t) m := by
      simp only [G,spatialLeviCivita,Matrix.mulVec,dotProduct,Fin.sum_univ_three,B,t,dh]
      ring
    calc
      _ = (M *ᵥ (B *ᵥ t)) a := Finset.sum_congr rfl (fun m _ => congrArg (fun s => M a m * s) (chr m))
      _ = t a := by rw [Matrix.mulVec_mulVec,hb,Matrix.one_mulVec]
  have metric (j k : I) : dh i j k =
      (∑ l : I, M j l * G l k) + ∑ l : I, M l k * G l j := by
    have tr : (∑ l : I, M l k * G l j) = ∑ l : I, M k l * G l j := Finset.sum_congr rfl
      (fun l _ => congrArg (fun s => s * G l j) (by simpa only [star_trivial] using (pos x hx).isHermitian.apply k l))
    rw [tr,connection_lower,connection_lower]
    have swap (p a b : I) : dh p a b=dh p b a := sym_h op pos hx p a b
    linarith only [swap i j k,swap k j i,swap j k i]

  ext a b
  have eq := metric a b
  simp only [dm,con,Matrix.add_apply,Matrix.transpose_apply,Matrix.mul_apply]
  simpa only [Fin.sum_univ_three,dh,M,G] using (by
    simp only [Fin.sum_univ_three] at eq ⊢; linarith only [eq] :
    dh i a b = (∑ l : I, G l a*M l b)+(∑ l:I, M a l*G l b))

private lemma dm_mul {f g : X → Mat} {x : X} (df : sm f x) (dg : sm g x) (i : I) :
    dm i (fun y => f y*g y) x = dm i f x*g x+f x*dm i g x := by
  ext a b
  simp only [dm,Matrix.mul_apply,Matrix.add_apply]
  rw [pd_sum (f:=fun k y => f y a k*g y k b) (fun k => ((df a k).mul (dg k b)).differentiableAt (by simp))]
  simp only [←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => pd_mul ((df a k).differentiableAt (by simp)) ((dg k b).differentiableAt (by simp)) i

private lemma sm_mul {f g : X → Mat} {x : X} (df : sm f x) (dg : sm g x) :
    sm (fun y => f y*g y) x := by
  intro a b
  change ContDiffAt ℝ ∞ (fun y => ∑ k : I, f y a k*g y k b) x
  exact ContDiffAt.sum fun k _ => (df a k).mul (dg k b)

private lemma dm_add {f g : X → Mat} {x : X} (df : sm f x) (dg : sm g x) (i : I) :
    dm i (fun z => f z+g z) x = dm i f x+dm i g x := by
  ext a b
  simp only [dm,pd,spatialADMPartial,Matrix.add_apply,fderiv_fun_add ((df a b).differentiableAt (by simp)) ((dg a b).differentiableAt (by simp)),ContinuousLinearMap.add_apply]

private lemma commute {h : X → Mat} {x : X} (dh : sm h x) (i j : I) :
    dm i (dm j h) x = dm j (dm i h) x := by
  ext a b
  let f := fun y => h y a b
  have df := ((dh a b).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have second (k l : I) : pd k (pd l f) x = fderiv ℝ (fderiv ℝ f) x (bvec k) (bvec l) := by
    unfold pd spatialADMPartial
    rw [fderiv_clm_apply (u:=fun _ : X => bvec l) df (differentiableAt_const _)]
    simp <;> rfl
  change pd i (pd j f) x = pd j (pd i f) x
  rw [second,second]
  exact (contDiffAt_infty.mp (dh a b) 2).isSymmSndFDerivAt (by simp) _ _

set_option maxHeartbeats 800000 in
theorem solution (W : Set ADMPoint) (op : IsOpen W) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (smooth : ∀ a b, ContDiffOn ℝ ∞ (fun y => h y a b) W)
    (pos : ∀ y∈W, (h y).PosDef) (x : ADMPoint) (hx : x∈W) :
    ∀ a b i j : Fin 3, (∑ k : Fin 3, h x a k * spatialRiemannCurvature h x k b i j) =
      -(∑ k : Fin 3, h x b k * spatialRiemannCurvature h x k a i j) := by
  classical
  have dh : sm h x := fun a b => (smooth a b).contDiffAt (op.mem_nhds hx)
  have dc (i : I) : sm (con h i) x := fun a b => sm_ch (pos x hx) dh a i b
  have dct (i : I) : sm (fun y => (con h i y)ᵀ) x := fun a b => dc i b a
  have twice (i j : I) : dm i (dm j h) x =
      ((dm i (con h j) x)ᵀ*h x+(con h j x)ᵀ*dm i h x) +
      (dm i h x*con h j x+h x*dm i (con h j) x) := by
    let A := fun y => (con h j y)ᵀ*h y
    let B := fun y => h y*con h j y
    have loc : dm j h =ᶠ[𝓝 x] (fun y => A y+B y) :=
      (show ∀ᶠ y in 𝓝 x, y∈W from op.mem_nhds hx).mono (fun y hy => metric_id op pos hy j)
    have der : dm i (dm j h) x = dm i (fun y => A y+B y) x := by
      ext a b
      have ev : (fun y => dm j h y a b) =ᶠ[𝓝 x] (fun y => (A y+B y) a b) :=
        loc.mono (fun _ eq => congrArg (fun m : Mat => m a b) eq)
      exact congrArg (fun L : X →L[ℝ] ℝ => L (bvec i)) ev.fderiv_eq
    rw [der,dm_add (sm_mul (dct j) dh) (sm_mul dh (dc j))]
    simp only [A,B,dm_mul (dct j) dh,dm_mul dh (dc j)]
    rfl
  intro a b i j
  let R := dm i (con h j) x - dm j (con h i) x + con h i x*con h j x - con h j x*con h i x
  have idR (k l : I) : R k l = spatialRiemannCurvature h x k l i j := by
    simp only [R,dm,con,Matrix.sub_apply,Matrix.add_apply,Matrix.mul_apply,spatialRiemannCurvature,Finset.sum_sub_distrib]
    ring
  have cancel : Rᵀ*h x+h x*R=0 := by
    have co := commute dh i j
    rw [twice i j,twice j i,metric_id op pos hx i,metric_id op pos hx j] at co
    have zero := sub_eq_zero.mpr co
    convert zero using 1
    dsimp only [R]
    simp only [Matrix.transpose_sub,Matrix.transpose_add,Matrix.transpose_mul]
    noncomm_ring
  have z := congrArg (fun m : Mat => m a b) cancel
  simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,idR,Matrix.zero_apply] at z
  have sym (k:I) : h x k b=h x b k := by simpa only [star_trivial] using (pos x hx).isHermitian.apply b k
  simp_rw [sym] at z
  simp only [Fin.sum_univ_three] at z ⊢
  linarith only [z]
