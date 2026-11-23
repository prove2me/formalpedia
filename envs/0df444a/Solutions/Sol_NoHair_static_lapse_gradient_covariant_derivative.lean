-- Prove2me | solution 1 for NoHair.static_lapse_gradient_covariant_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:25:27.533921+00:00
-- url     : https://prove2.me/submissions/35589a58-a63b-4686-84fe-322c67cc0ef3

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

theorem solution (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hn : ContDiffOn ℝ ∞ N W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (x : ADMPoint) (hx : x ∈ W) (i : Fin 3) :
    (∀ a : Fin 3, spatialADMPartial i (staticRaisedGradient N h a) x +
      (∑ l : Fin 3, spatialLeviCivita h x a i l * staticRaisedGradient N h l x) =
      ∑ j : Fin 3, (h x)⁻¹ a j * staticSpatialHessian N h i j x) ∧
    spatialADMPartial i (staticLapseGradientSq N h) x =
      2 * ∑ j : Fin 3, staticSpatialHessian N h i j x * staticRaisedGradient N h j x := by
  classical
  let M := h x
  let B := (h x)⁻¹
  let n := fun j => pd j N x
  let v := fun j => staticRaisedGradient N h j x
  let dv := fun j => pd i (staticRaisedGradient N h j) x
  let dh := fun t a b => pd t (fun y => h y a b) x
  let G := fun a l => spatialLeviCivita h x a i l
  let P := fun j => staticSpatialHessian N h i j x
  have ch (a b : I) := (hh a b).contDiffAt (hw.mem_nhds hx)
  have cn := hn.contDiffAt (hw.mem_nhds hx)
  have cv (j : I) := sm_grad (hp x hx) ch cn j
  have detU := (h x).isUnit_iff_isUnit_det.mp (hp x hx).isUnit
  have bh : B*M=1 := Matrix.nonsing_inv_mul _ detU
  have hb : M*B=1 := Matrix.mul_nonsing_inv _ detU
  have lower_at (y : X) (hy : y ∈ W) (j : I) :
      ∑ k : I, h y j k * staticRaisedGradient N h k y = pd j N y := by
    let w := fun k => pd k N y
    change ((h y) *ᵥ ((h y)⁻¹ *ᵥ w)) j = w j
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ ((h y).isUnit_iff_isUnit_det.mp (hp y hy).isUnit),Matrix.one_mulVec]
  have lower (j : I) : ∑ k : I, M j k * v k = n j := lower_at x hx j
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
      (fun l _ => congrArg (fun s => s * G l j) (by simpa only [star_trivial] using (hp x hx).isHermitian.apply k l))
    rw [tr,connection_lower,connection_lower]
    have swap (p a b : I) : dh p a b=dh p b a := sym_h hw hp hx p a b
    linarith only [swap i j k,swap k j i,swap j k i]
  have dlow (j : I) : pd i (pd j N) x =
      ∑ k : I, (dh i j k * v k + M j k * dv k) := by
    have ev : (fun y => ∑ k : I, h y j k * staticRaisedGradient N h k y) =ᶠ[𝓝 x] pd j N :=
      (show ∀ᶠ y in 𝓝 x, y ∈ W from hw.mem_nhds hx).mono fun y hy => lower_at y hy j
    calc
      _ = pd i (fun y => ∑ k : I, h y j k * staticRaisedGradient N h k y) x :=
        congrArg (fun L : X →L[ℝ] ℝ => L (bvec i)) ev.symm.fderiv_eq
      _ = _ := by
        rw [pd_sum (f:=fun k y => h y j k * staticRaisedGradient N h k y)
          (fun k => ((ch j k).mul (cv k)).differentiableAt (by simp))]
        exact Finset.sum_congr rfl fun k _ => pd_mul ((ch j k).differentiableAt (by simp))
          ((cv k).differentiableAt (by simp)) i
  let a := fun k => dv k + ∑ l : I, G k l * v l
  have lowered : M *ᵥ a = P := by
    funext j
    change (∑ k : I, M j k * (dv k + ∑ l : I, G k l * v l)) =
      pd i (pd j N) x - ∑ k : I, G k j * n k
    rw [dlow]
    simp_rw [metric,← lower]
    simp only [Fin.sum_univ_three]
    ring
  have raised : a = B *ᵥ P := by rw [← lowered,Matrix.mulVec_mulVec,bh,Matrix.one_mulVec]
  refine ⟨fun j => congrFun raised j,?_⟩
  have grad (j : I) : dv j = (∑ l : I, B j l*P l) - ∑ l : I, G j l*v l := by
    have h := congrFun raised j
    change dv j + _ = ∑ l : I, B j l*P l at h
    linarith only [h]
  have hes (j : I) : pd i (pd j N) x = P j + ∑ l : I, G l j*n l := by
    dsimp only [P,staticSpatialHessian,G,n,pd]
    ring
  have sb (a b : I) : B a b=B b a := by
    simpa only [star_trivial] using (hp x hx).inv.isHermitian.apply b a
  have vv (k : I) : v k = ∑ l : I, B k l*n l := rfl
  change pd i (fun y => ∑ k : I, pd k N y * staticRaisedGradient N h k y) x = _
  rw [pd_sum (f:=fun k y => pd k N y * staticRaisedGradient N h k y)
    (fun k => ((sm_pd cn k).mul (cv k)).differentiableAt (by simp))]
  have e (j : I) : pd i (fun y => pd j N y * staticRaisedGradient N h j y) x =
      (P j+∑ l : I, G l j*n l)*v j+n j*((∑ l : I, B j l*P l) - ∑ l : I, G j l*v l) := by
    rw [pd_mul ((sm_pd cn j).differentiableAt (by simp)) ((cv j).differentiableAt (by simp))]
    change pd i (pd j N) x*v j + n j*dv j = _
    rw [hes,grad]
  simp_rw [e]
  change _ = 2 * ∑ k : I, P k * v k
  simp_rw [vv]
  simp only [Fin.sum_univ_three,sb 1 0,sb 2 0,sb 2 1]
  ring
