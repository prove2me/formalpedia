-- Prove2me | solution 2 for NoHair.spatial_conformal_ricci_three
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:54:36.06793+00:00
-- url     : https://prove2.me/submissions/90539ee4-a068-4d0e-9cf8-f8eb65f766e3

import Theorems.Thm_NoHair_spatial_conformal_connection
import Theorems.Thm_NoHair_static_lapse_gradient_covariant_derivative

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


set_option maxHeartbeats 6500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

private def kr (a i : I) : ℝ := if a=i then 1 else 0

private def corr (g : Mat) (q v : I → ℝ) (a i j : I) : ℝ :=
  kr a i*q j+kr a j*q i-g i j*v a

private def dcorr (g : Mat) (G : I → I → I → ℝ) (H S : Mat) (q v : I → ℝ)
    (k a i j : I) : ℝ :=
  kr a i*(H k j+∑ t, G t k j*q t) + kr a j*(H k i+∑ t, G t k i*q t) -
    ((∑ t, g i t*G t k j)+(∑ t, g t j*G t k i))*v a -
    g i j*(S k a-∑ t, G a k t*v t)

private lemma linear_terms (g : Mat) (G : I → I → I → ℝ) (H S : Mat) (q v : I → ℝ)
    (sg : ∀ i j, g i j=g j i) (sG : ∀ a i j, G a i j=G a j i) (sH : ∀ i j,H i j=H j i)
    (lv : ∀ i, ∑ a,g i a*v a=q i) (lH : ∀ j i, ∑ a,g i a*S j a=H j i) (i j : I) :
    (∑ a, (dcorr g G H S q v a a j i - dcorr g G H S q v j a a i +
      ∑ t, (G a a t*corr g q v t j i+corr g q v a a t*G t j i -
        G a j t*corr g q v t a i-corr g q v a j t*G t a i))) =
      -H i j-g i j*(∑ a, S a a) := by
  let err := (∑ a, g i a*S j a)-H j i
  have zero : err=0 := sub_eq_zero.mpr (lH j i)
  rw [← add_zero (-H i j-g i j*(∑ a,S a a)),← zero]
  dsimp only [err,dcorr,corr]
  simp_rw [← lv]
  have cases3 : ∀ k : I, k=0 ∨ k=1 ∨ k=2 := by decide
  rcases cases3 i with rfl|rfl|rfl <;> rcases cases3 j with rfl|rfl|rfl <;>
    simp only [Fin.sum_univ_three,kr,ite_true,if_pos rfl,
      if_neg (by decide : (0:I) ≠ 1),if_neg (by decide : (0:I) ≠ 2),
      if_neg (by decide : (1:I) ≠ 0),if_neg (by decide : (1:I) ≠ 2),
      if_neg (by decide : (2:I) ≠ 0),if_neg (by decide : (2:I) ≠ 1),
      sg 1 0,sg 2 0,sg 2 1,sG _ 1 0,sG _ 2 0,sG _ 2 1,sH 1 0,sH 2 0,sH 2 1,one_mul,zero_mul] <;> ring

private lemma quadratic_terms (g : Mat) (q v : I → ℝ) (sg : ∀ i j,g i j=g j i)
    (lv : ∀ i, ∑ a,g i a*v a=q i) (i j : I) :
    (∑ a, (-(1/2:ℝ)*q a*corr g q v a j i+(1/2:ℝ)*q j*corr g q v a a i+
      ∑ t, (corr g q v a a t*corr g q v t j i-corr g q v a j t*corr g q v t a i))) =
    (3/2:ℝ)*q i*q j-(1/2:ℝ)*g i j*(∑ a,q a*v a) := by
  dsimp only [corr]
  simp_rw [← lv]
  have cases3 : ∀ k : I, k=0 ∨ k=1 ∨ k=2 := by decide
  rcases cases3 i with rfl|rfl|rfl <;> rcases cases3 j with rfl|rfl|rfl <;>
    simp only [Fin.sum_univ_three,kr,ite_true,if_pos rfl,
      if_neg (by decide : (0:I) ≠ 1),if_neg (by decide : (0:I) ≠ 2),
      if_neg (by decide : (1:I) ≠ 0),if_neg (by decide : (1:I) ≠ 2),
      if_neg (by decide : (2:I) ≠ 0),if_neg (by decide : (2:I) ≠ 1),
      sg 1 0,sg 2 0,sg 2 1,one_mul,zero_mul] <;> ring

private lemma expand_ric (G C : I → I → I → ℝ) (dg dc : I → I → I → I → ℝ)
    (q : I → ℝ) (s : ℝ) (i j : I) :
    (∑ a, (dg a a j i - s^2/2*q a*C a j i+s*dc a a j i -
      (dg j a a i - s^2/2*q j*C a a i+s*dc j a a i) +
      ∑ t, ((G a a t+s*C a a t)*(G t j i+s*C t j i)-
        (G a j t+s*C a j t)*(G t a i+s*C t a i)))) =
      (∑ a, (dg a a j i-dg j a a i+∑ t, (G a a t*G t j i-G a j t*G t a i))) +
      s*(∑ a, (dc a a j i-dc j a a i+∑ t, (G a a t*C t j i+C a a t*G t j i-
          G a j t*C t a i-C a j t*G t a i))) +
      s^2*(∑ a, (-(1/2:ℝ)*q a*C a j i+(1/2:ℝ)*q j*C a a i+
        ∑ t, (C a a t*C t j i-C a j t*C t a i))) := by
  simp only [Fin.sum_univ_three]
  ring

private lemma pd_add {f g : X → ℝ} {x : X} (cf : DifferentiableAt ℝ f x)
    (cg : DifferentiableAt ℝ g x) (i : I) :
    pd i (fun y => f y+g y) x = pd i f x+pd i g x := by
  unfold pd spatialADMPartial; rw [fderiv_fun_add cf cg]; rfl

private lemma pd_sub {f g : X → ℝ} {x : X} (cf : DifferentiableAt ℝ f x)
    (cg : DifferentiableAt ℝ g x) (i : I) :
    pd i (fun y => f y-g y) x = pd i f x-pd i g x := by
  unfold pd spatialADMPartial; rw [fderiv_fun_sub cf cg]; rfl

private lemma pd_cmul {f : X → ℝ} {x : X} (cf : DifferentiableAt ℝ f x) (z : ℝ) (i : I) :
    pd i (fun y => z*f y) x = z*pd i f x := by
  unfold pd spatialADMPartial; rw [fderiv_const_mul cf z]; rfl

private lemma second_pd {u : X → ℝ} {x : X} (cu : ContDiffAt ℝ ∞ u x) (i j : I) :
    pd i (pd j u) x = pd j (pd i u) x := by
  have hcd := (cu.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have ex (a b : I) : pd a (pd b u) x = fderiv ℝ (fderiv ℝ u) x (bvec a) (bvec b) := by
    change fderiv ℝ (fun y => fderiv ℝ u y (bvec b)) x (bvec a) = _
    rw [fderiv_clm_apply hcd (differentiableAt_const (bvec b))]
    simp
  rw [ex,ex]
  exact cu.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞) ≤ ⊤)) _ _

theorem solution (u : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hu : ContDiffOn ℝ ∞ u W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (x : ADMPoint) (hx : x ∈ W) (hn : u x ≠ 0) :
    ∀ i j : Fin 3, spatialRicciTensor (fun y => (u y ^ 4) • h y) x i j =
      spatialRicciTensor h x i j - (2 / u x) * staticSpatialHessian u h i j x -
      (2 / u x) * h x i j *
        (∑ a : Fin 3, ∑ b : Fin 3, (h x)⁻¹ a b * staticSpatialHessian u h a b x) +
      (6 / u x ^ 2) * spatialADMPartial i u x * spatialADMPartial j u x -
      (2 / u x ^ 2) * h x i j * staticLapseGradientSq u h x := by
  classical
  let M := h x
  let B := (h x)⁻¹
  let G := spatialLeviCivita h x
  let H : Mat := fun i j => staticSpatialHessian u h i j x
  let S : Mat := fun i a => ∑ j, B a j * H i j
  let q := fun i => pd i u x
  let v := fun a => staticRaisedGradient u h a x
  let s := fun y => 2/u y
  let k := fun y => u y^4 • h y
  let cf := fun a i j y => corr (h y) (fun t => pd t u y) (fun t => staticRaisedGradient u h t y) a i j
  let C := corr M q v
  let dc := dcorr M G H S q v
  let dg := fun t a i j => pd t (fun y => spatialLeviCivita h y a i j) x
  have ch (i j : I) := (hh i j).contDiffAt (hw.mem_nhds hx)
  have cu := hu.contDiffAt (hw.mem_nhds hx)
  have dq (i : I) := (sm_pd cu i).differentiableAt (by simp)
  have dv (i : I) := (sm_grad (hp x hx) ch cu i).differentiableAt (by simp)
  have dh (i j : I) := (ch i j).differentiableAt (by simp)
  have dG (a i j : I) := (sm_ch (hp x hx) ch a i j).differentiableAt (by simp)
  have cs : ContDiffAt ℝ ∞ (fun y => (2:ℝ)/u y) x :=
    (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : X => (2:ℝ)) x).fun_div cu hn
  have dS : DifferentiableAt ℝ s x := cs.differentiableAt (by simp)
  have nz : ∀ᶠ y in 𝓝 x, u y ≠ 0 := cu.continuousAt.eventually_ne hn
  have wmem : ∀ᶠ y in 𝓝 x, y∈W := hw.mem_nhds hx
  have dscale (t : I) : pd t s x = -(s x)^2/2*q t := by
    have ev : (fun y => s y*u y) =ᶠ[𝓝 x] (fun _ => (2:ℝ)) :=
      nz.mono fun y hy => div_mul_cancel₀ _ hy
    have e := congrArg (fun A : X →L[ℝ] ℝ => A (bvec t)) ev.fderiv_eq
    change pd t (fun y => s y*u y) x = pd t (fun _ => (2:ℝ)) x at e
    rw [pd_mul dS (cu.differentiableAt (by simp))] at e
    have ez : pd t (fun _ => (2:ℝ)) x = 0 := by simp [pd,spatialADMPartial]
    rw [ez] at e
    change pd t s x*u x + 2/u x * q t=0 at e
    change pd t s x= -(2/u x)^2/2*q t
    field_simp [hn] at e ⊢
    linarith only [e]
  have sg (i j : I) : M i j=M j i := by simpa only [star_trivial] using (hp x hx).isHermitian.apply j i
  have sG (a i j : I) : G a i j=G a j i := by
    dsimp only [G,spatialLeviCivita]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    have e:=sym_h hw hp hx t i j
    change spatialADMPartial t (fun y => h y i j) x = _ at e
    rw [e]
    ring
  have sH (i j : I) : H i j=H j i := by
    dsimp only [H,staticSpatialHessian]
    rw [show spatialADMPartial i (spatialADMPartial j u) x=spatialADMPartial j (spatialADMPartial i u) x from second_pd cu i j]
    exact congrArg (_ - ·) (Finset.sum_congr rfl (fun k _ => congrArg (· * spatialADMPartial k u x) (sG k i j)))
  have detU := (h x).isUnit_iff_isUnit_det.mp (hp x hx).isUnit
  have hb : M*B=1 := Matrix.mul_nonsing_inv _ detU
  have lv (j : I) : ∑ t,M j t*v t=q j := by
    change (M *ᵥ (B *ᵥ q)) j=q j
    rw [Matrix.mulVec_mulVec,hb,Matrix.one_mulVec]
  have lH (j i : I) : ∑ a,M i a*S j a=H j i := by
    change (M *ᵥ (B *ᵥ H j)) i=H j i
    rw [Matrix.mulVec_mulVec,hb,Matrix.one_mulVec]
  let dm := fun t a b => pd t (fun y => h y a b) x
  have lower_conn (i a l : I) : ∑ t,M a t*G t i l = (dm i a l+dm l a i-dm a i l)/2 := by
    let w := fun k => (dm i k l+dm l k i-dm k i l)/2
    have eq (t : I) : G t i l=(B *ᵥ w) t := by
      simp only [G,spatialLeviCivita,Matrix.mulVec,dotProduct,Fin.sum_univ_three,B,w,dm,pd]
      ring
    calc
      _ = (M *ᵥ (B *ᵥ w)) a := Finset.sum_congr rfl (fun t _ => congrArg (fun e => M a t*e) (eq t))
      _ = w a := by rw [Matrix.mulVec_mulVec,hb,Matrix.one_mulVec]
  have metric (k i j : I) : dm k i j=(∑ t,M i t*G t k j)+(∑ t,M t j*G t k i) := by
    have tr : (∑ t,M t j*G t k i)=∑ t,M j t*G t k i :=
      Finset.sum_congr rfl fun t _ => congrArg (· * G t k i) (sg t j)
    rw [tr,lower_conn,lower_conn]
    have sw (t b c : I) : dm t b c=dm t c b := sym_h hw hp hx t b c
    linarith only [sw k i j,sw j i k,sw i j k]
  have hes (t j : I) : pd t (pd j u) x=H t j+∑ b,G b t j*q b := by
    dsimp only [H,G,q,staticSpatialHessian,pd]
    ring
  have grad (t a : I) : pd t (staticRaisedGradient u h a) x=S t a-∑ b,G a t b*v b := by
    have e := (static_lapse_gradient_covariant_derivative u h W hw hu hh hp x hx t).1 a
    change pd t (staticRaisedGradient u h a) x+_=S t a at e
    linarith only [e]
  have dCF (a i j : I) : DifferentiableAt ℝ (cf a i j) x :=
    (((dq j).const_mul (kr a i)).add ((dq i).const_mul (kr a j))).sub ((dh i j).mul (dv a))
  have dcval (t a i j : I) : pd t (cf a i j) x = dc t a i j := by
    change pd t (fun y => (kr a i*pd j u y+kr a j*pd i u y)-h y i j*staticRaisedGradient u h a y) x=_
    rw [pd_sub (f:=fun y => kr a i*pd j u y+kr a j*pd i u y) (g:=fun y => h y i j*staticRaisedGradient u h a y)
        (((dq j).const_mul _).add ((dq i).const_mul _)) ((dh i j).mul (dv a)),
        pd_add (f:=fun y => kr a i*pd j u y) (g:=fun y => kr a j*pd i u y) ((dq j).const_mul _) ((dq i).const_mul _),
        pd_cmul (dq j),pd_cmul (dq i),pd_mul (dh i j) (dv a)]
    change kr a i*pd t (pd j u) x+kr a j*pd t (pd i u) x-
      (dm t i j*v a+M i j*pd t (staticRaisedGradient u h a) x)=_
    rw [hes,hes,metric,grad]
    dsimp only [dc,dcorr]
    ring
  have eqn (y : X) (hy : y∈W) (hnz : u y≠0) (a i j : I) :
      spatialLeviCivita k y a i j=spatialLeviCivita h y a i j+s y*cf a i j y := by
    rw [(spatial_conformal_connection u h W hw hu hh hp y hy hnz).2]
    dsimp only [s,cf,corr,kr]
    ring
  have eq0 (a i j : I) : spatialLeviCivita k x a i j=G a i j+s x*C a i j := eqn x hx hn a i j
  have eq1 (t a i j : I) : pd t (fun y => spatialLeviCivita k y a i j) x =
      dg t a i j - (s x)^2/2*q t*C a i j+s x*dc t a i j := by
    have ev : (fun y => spatialLeviCivita k y a i j) =ᶠ[𝓝 x]
        (fun y => spatialLeviCivita h y a i j+s y*cf a i j y) :=
      (wmem.and nz).mono fun y hy => eqn y hy.1 hy.2 a i j
    have de := congrArg (fun A : X →L[ℝ] ℝ => A (bvec t)) ev.fderiv_eq
    change pd t _ x=pd t (fun y => spatialLeviCivita h y a i j+s y*cf a i j y) x at de
    rw [de,pd_add (f:=fun y => spatialLeviCivita h y a i j) (g:=fun y => s y*cf a i j y)
      (dG a i j) (dS.mul (dCF a i j)),pd_mul dS (dCF a i j),dscale,dcval]
    change dg t a i j+(-(s x)^2/2*q t*C a i j+s x*dc t a i j)=_
    ring
  intro i j
  change spatialRicciTensor k x i j=_
  have e : spatialRicciTensor k x i j =
      spatialRicciTensor h x i j+s x*(-H i j-M i j*∑ a,S a a)+
      (s x)^2*((3/2:ℝ)*q i*q j-(1/2:ℝ)*M i j*∑ a,q a*v a) := by
    unfold spatialRicciTensor
    change (∑ a,(pd a (fun y => spatialLeviCivita k y a j i) x -
      pd j (fun y => spatialLeviCivita k y a a i) x+∑ t,(spatialLeviCivita k x a a t*spatialLeviCivita k x t j i-
      spatialLeviCivita k x a j t*spatialLeviCivita k x t a i)))=_
    simp_rw [eq1,eq0]
    rw [expand_ric G C dg dc q (s x) i j,linear_terms M G H S q v sg sG sH lv lH i j,
      quadratic_terms M q v sg lv i j]
  rw [e]
  change spatialRicciTensor h x i j+2/u x*(-H i j-M i j*(∑ a,S a a))+
      (2/u x)^2*((3/2:ℝ)*q i*q j-(1/2:ℝ)*M i j*(∑ a,q a*v a))=
      spatialRicciTensor h x i j-2/u x*H i j-2/u x*M i j*(∑ a,S a a)+
      6/u x^2*q i*q j-2/u x^2*M i j*(∑ a,q a*v a)
  field_simp [hn]
  ring
