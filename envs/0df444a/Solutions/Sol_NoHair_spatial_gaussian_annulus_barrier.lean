-- Prove2me | solution 1 for NoHair.spatial_gaussian_annulus_barrier
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:28:07.225141+00:00
-- url     : https://prove2.me/submissions/96f6cf88-4db1-448b-8f50-7701ff5edf61

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

private lemma d_cmul' {f : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : I) :
    pd i (fun y => c*f y) x = c*pd i f x := by
  unfold pd spatialADMPartial
  rw [(hf.hasFDerivAt.const_mul c).fderiv]; rfl

set_option maxHeartbeats 650000 in
theorem solution (W : Set ADMPoint) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hw : IsOpen W) (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (y : ADMPoint) (r : ℝ) (hr : 0<r) (ball : Metric.closedBall y r ⊆ W) :
    ∃ α : ℝ, 0 < α ∧
      let b := fun t : ADMPoint => Real.exp (-α * ‖t-y‖^2) - Real.exp (-α*r^2)
      ContDiff ℝ ∞ b ∧ (∀ x : ADMPoint, r/2 ≤ dist x y → dist x y ≤ r →
        0 < (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian b h i j x)) ∧
      ∀ x : ADMPoint, dist x y = r → fderiv ℝ b x ≠ 0 := by
  classical
  let v := fun (i : I) (t : X) => t i-y i
  let R := fun t : X => ‖t-y‖^2
  let δ := fun i j : I => if i=j then (1:ℝ) else 0
  let A := fun t : X => ∑ i : I, ∑ j : I, (h t)⁻¹ i j * (v i t*v j t)
  let T := fun t : X => ∑ i : I, ∑ j : I, (h t)⁻¹ i j * (δ i j -
    ∑ l : I, spatialLeviCivita h t l i j*v l t)
  let K := Metric.closedBall y r ∩ {x : X | r/2 ≤ dist x y}
  have ck : IsCompact K := (isCompact_closedBall y r).inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have ch {x : X} (wx : x ∈ W) (i j : I) := (hh i j).contDiffAt (hw.mem_nhds wx)
  let pr (i : I) : X →L[ℝ] ℝ := PiLp.proj 2 (fun _ : I => ℝ) i
  have cv (i : I) : ContDiff ℝ ∞ (v i) := by
    change ContDiff ℝ ∞ (fun t : X => pr i t-y i)
    exact (pr i).contDiff.sub contDiff_const
  have form : R = fun t => ∑ i : I, (v i t)^2 := by funext t; exact EuclideanSpace.real_norm_sq_eq (t-y)
  have cR : ContDiff ℝ ∞ R := by rw [form]; exact ContDiff.sum fun i _ => (cv i).pow 2
  have posA (x : X) (hx : x∈K) : 0 < A x := by
    have n0 : (fun i => v i x) ≠ 0 := by
      intro eq
      have xy : x=y := by ext i; exact sub_eq_zero.mp (congrFun eq i)
      have dr : r/2 ≤ dist x y := hx.2
      rw [xy,dist_self] at dr
      linarith only [hr,dr]
    have z := (hp x (ball hx.1)).inv.dotProduct_mulVec_pos n0
    simp only [star_trivial] at z
    calc
      0 < _ := z
      _ = A x := by simp only [A,dotProduct,Matrix.mulVec,Fin.sum_univ_three]; ring
  have ca (x : X) (wx : x∈W) : ContDiffAt ℝ ∞ A x := ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (sm_inv (hp x wx) (ch wx) i j).mul ((cv i).contDiffAt.mul (cv j).contDiffAt)
  have ct (x : X) (wx : x∈W) : ContDiffAt ℝ ∞ T x := ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (sm_inv (hp x wx) (ch wx) i j).mul (contDiffAt_const.sub (ContDiffAt.sum fun l _ =>
      (sm_ch (hp x wx) (ch wx) l i j).mul (cv l).contDiffAt))
  have cratio : ContinuousOn (fun t => T t/A t) K := fun x hx =>
    ((ct x (ball hx.1)).continuousAt.div (ca x (ball hx.1)).continuousAt (posA x hx).ne').continuousWithinAt
  obtain ⟨D,bound⟩ := (ck.image_of_continuousOn cratio).bddAbove
  let α := max D 0 + 1
  have ap : 0<α := by dsimp only [α]; linarith only [le_max_right D 0]
  let g := fun t => Real.exp (-α*R t)
  let b := fun t => g t-Real.exp (-α*r^2)
  have cg : ContDiff ℝ ∞ g := Real.contDiff_exp.comp (contDiff_const.mul cR)
  have cb : ContDiff ℝ ∞ b := cg.sub contDiff_const
  have dv (i j : I) (x : X) : pd i (v j) x = δ i j := by
    have d := (((pr j).hasFDerivAt (x:=x)).sub_const (y j)).fderiv
    change fderiv ℝ (v j) x = _ at d
    change fderiv ℝ (v j) x (bvec i) = _
    rw [d]
    change (EuclideanSpace.single i (1:ℝ)) j=_
    simp [δ,PiLp.single_apply,eq_comm]
  have dr (i : I) (x : X) : pd i R x=2*v i x := by
    have sq (j : I) : pd i (fun t => (v j t)^2) x = 2*v j x*δ i j := by
      have d := (((cv j).differentiable (by simp) x).hasFDerivAt.pow 2).fderiv
      change fderiv ℝ (fun t => (v j t)^2) x (bvec i)=_
      rw [d]
      simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,nsmul_eq_mul]
      change 2*v j x^(2-1)*pd i (v j) x = _
      rw [dv]; norm_num
    rw [form,pd_sum (f:=fun j t => (v j t)^2) (fun j => ((cv j).pow 2).differentiable (by simp) x)]
    simp only [sq]
    simp [δ,mul_ite]
  have dg (i : I) (x : X) : pd i g x = -2*α*g x*v i x := by
    have d := ((Real.hasDerivAt_exp _).comp_hasFDerivAt x (((cR.differentiable (by simp) x).hasFDerivAt).const_mul (-α))).fderiv
    change fderiv ℝ g x = _ at d
    change fderiv ℝ g x (bvec i) = _
    rw [d]
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
    change g x * (-α*pd i R x) = _
    rw [dr]; ring
  have dB (i : I) (x : X) : pd i b x = -2*α*g x*v i x := by
    have d := ((cg.differentiable (by simp) x).hasFDerivAt.sub_const (Real.exp (-α*r^2))).fderiv
    change fderiv ℝ b x = _ at d
    exact (congrArg (fun L : X →L[ℝ] ℝ => L (bvec i)) d).trans (dg i x)
  have dd (i j : I) (x : X) : pd i (pd j b) x = 4*α^2*g x*v i x*v j x -2*α*g x*δ i j := by
    have f : pd j b = fun t => (-2*α)*(g t*v j t) := funext fun t => (dB j t).trans (mul_assoc _ _ _)
    rw [f,d_cmul' (f:=fun t => g t*v j t) ((cg.mul (cv j)).differentiable (by simp) x),
      pd_mul (f:=g) (g:=v j) (cg.differentiable (by simp) x) ((cv j).differentiable (by simp) x),dg,dv]
    ring
  have H (i j : I) (x : X) : staticSpatialHessian b h i j x =
      2*α*g x*(2*α*(v i x*v j x)-(δ i j-∑ l : I, spatialLeviCivita h x l i j*v l x)) := by
    change pd i (pd j b) x - (∑ l : I, spatialLeviCivita h x l i j*pd l b x) = _
    simp only [dd,dB,Fin.sum_univ_three]; ring
  refine ⟨α,ap,cb,?_,?_⟩
  · intro x lo hi
    have hx : x∈K := ⟨Metric.mem_closedBall.mpr hi,lo⟩
    have bnd : T x/A x≤D := bound ⟨x,hx,rfl⟩
    have less : T x < (2*α)*A x := lt_of_le_of_lt ((div_le_iff₀ (posA x hx)).mp bnd)
      (mul_lt_mul_of_pos_right (by dsimp [α]; linarith only [le_max_left D 0,le_max_right D 0]) (posA x hx))
    have val : 0< 2*α*g x*(2*α*A x-T x) := mul_pos (mul_pos (mul_pos (by norm_num) ap) (Real.exp_pos _)) (sub_pos.mpr less)
    change 0 < ∑ i : I, ∑ j : I, (h x)⁻¹ i j*staticSpatialHessian b h i j x
    exact val.trans_eq (by simp only [A,T,H,Fin.sum_univ_three]; ring)
  · intro x rxy zero
    change fderiv ℝ b x=0 at zero
    have xy : x=y := by
      ext i
      have zz : pd i b x=0 := by simp only [pd,spatialADMPartial,zero,ContinuousLinearMap.zero_apply]
      have gg : -2*α*g x ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ap.ne') (Real.exp_pos _).ne'
      exact sub_eq_zero.mp ((mul_eq_zero.mp ((dB i x).symm.trans zz)).resolve_left gg)
    rw [xy,dist_self] at rxy
    linarith
