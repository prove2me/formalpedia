-- Prove2me | solution 1 for NoHair.spatial_conformal_ricci_three
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:28:06.381425+00:00
-- url     : https://prove2.me/submissions/cdc6ab74-9daa-4d4e-9a86-d0987ce4a1b7

import Definitions.Def_NoHair_conformalConnectionContractions
import Theorems.Thm_NoHair_spatial_conformal_connection
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

private noncomputable abbrev fourth (u : X → ℝ) (h : X → Mat) (y : X) : Mat :=
  (u y ^ 4) • h y

open NoHair.ConformalConnection (kr deltaSum connectionChange quadratic mixed mixed_contraction quadratic_contraction quadratic_add)


private lemma ricci_parts (h : X → Mat) (x : X) (i j : I) :
    spatialRicciTensor h x i j =
    (∑ a : I, spatialADMPartial a (fun y => spatialLeviCivita h y a j i) x) -
    (∑ a : I, spatialADMPartial j (fun y => spatialLeviCivita h y a a i) x) + quadratic (spatialLeviCivita h x) i j := by
  simp only [spatialRicciTensor,quadratic,Finset.sum_add_distrib,Finset.sum_sub_distrib]

private lemma d_sym {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x) (i j : I) :
    pd i (pd j f) x = pd j (pd i f) x := by
  have h2 : ContDiffAt ℝ 2 f x := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have c := (h2.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
  have der (a b : I) : pd a (pd b f) x = fderiv ℝ (fderiv ℝ f) x (bvec a) (bvec b) := by
    unfold pd spatialADMPartial
    rw [fderiv_clm_apply (u := fun _ : X => EuclideanSpace.single b 1) c
      (differentiableAt_const (EuclideanSpace.single b 1))]
    simp [bvec]
  rw [der,der]
  exact h2.isSymmSndFDerivAt (by simp) _ _

private lemma d_add {f g : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : I) :
    pd i (fun y => f y+g y) x=pd i f x+pd i g x := by
  have H := (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y+g y) x = _ at H
  unfold pd spatialADMPartial
  rw [H]; rfl

private lemma d_sub {f g : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : I) :
    pd i (fun y => f y-g y) x=pd i f x-pd i g x := by
  have H := (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y-g y) x = _ at H
  unfold pd spatialADMPartial
  rw [H]; rfl

private lemma d_cmul {f : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : I) :
    pd i (fun y => c*f y) x = c*pd i f x := by
  unfold pd spatialADMPartial
  rw [(hf.hasFDerivAt.const_mul c).fderiv]; rfl

private lemma metric_comp {W : Set X} {h : X → Mat} (ow : IsOpen W)
    (hp : ∀ y ∈ W, (h y).PosDef) {x : X} (hx : x∈W) (i j k : I) :
    pd i (fun y => h y j k) x =
      (∑ l : I, h x j l * spatialLeviCivita h x l i k) +
      ∑ l : I, h x l k * spatialLeviCivita h x l i j := by
  let M := h x
  let B := (h x)⁻¹
  let dh := fun t a b => pd t (fun y => h y a b) x
  let G := fun a l => spatialLeviCivita h x a i l
  have hb : M*B=1 := Matrix.mul_nonsing_inv _ ((h x).isUnit_iff_isUnit_det.mp (hp x hx).isUnit)
  have lower (a l : I) : ∑ m : I, M a m * G m l = (dh i a l + dh l a i - dh a i l)/2 := by
    let v := fun k => (dh i k l + dh l k i - dh k i l)/2
    have chr (m : I) : G m l = (B *ᵥ v) m := by
      simp only [G,spatialLeviCivita,Matrix.mulVec,dotProduct,Fin.sum_univ_three,B,v,dh]
      ring
    calc
      _ = (M *ᵥ (B *ᵥ v)) a := Finset.sum_congr rfl (fun m _ => congrArg (fun s => M a m * s) (chr m))
      _ = v a := by rw [Matrix.mulVec_mulVec,hb,Matrix.one_mulVec]
  change dh i j k = (∑ l : I, M j l * G l k) + ∑ l : I, M l k * G l j
  have tr : (∑ l : I, M l k * G l j) = ∑ l : I, M k l * G l j := Finset.sum_congr rfl
    (fun l _ => congrArg (fun s => s * G l j) (by simpa only [star_trivial] using (hp x hx).isHermitian.apply k l))
  rw [tr,lower,lower]
  have swap (t a b : I) : dh t a b = dh t b a := sym_h ow hp hx t a b
  linarith only [swap i j k,swap k j i,swap j k i]

set_option maxHeartbeats 800000 in
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
  let k := fourth u h
  let z := fun y => 2/u y
  let p := fun (i : I) y => z y * pd i u y
  let q := fun (i : I) y => z y * staticRaisedGradient u h i y
  let C := fun y => connectionChange (h y) (fun i => p i y) (fun i => q i y)
  let G := spatialLeviCivita h x
  let P := fun i => p i x
  let Q := fun i => q i x
  let dp := fun t i => pd t (p i) x
  let dq := fun t a => pd t (q a) x
  let H := fun i j => staticSpatialHessian u h i j x
  let n := fun i : I => pd i u x
  let E := staticLapseGradientSq u h x
  let L := ∑ i : I, ∑ j : I, (h x)⁻¹ i j * H i j
  have cn := hu.contDiffAt (hw.mem_nhds hx)
  have ch (i j : I) := (hh i j).contDiffAt (hw.mem_nhds hx)
  have cz : ContDiffAt ℝ ∞ z x := contDiffAt_const.div cn hn
  have cp (i : I) : ContDiffAt ℝ ∞ (p i) x := cz.mul (sm_pd cn i)
  have cq (i : I) : ContDiffAt ℝ ∞ (q i) x := cz.mul (sm_grad (hp x hx) ch cn i)
  have cc (a i j : I) : ContDiffAt ℝ ∞ (fun y => C y a i j) x :=
    ((contDiffAt_const.mul (cp j)).add (contDiffAt_const.mul (cp i))).sub ((ch i j).mul (cq a))
  have sym (i j : I) : h x i j=h x j i := by simpa only [star_trivial] using (hp x hx).isHermitian.apply j i
  have gs (a i j : I) : G a i j=G a j i := by
    dsimp only [G,spatialLeviCivita]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    have e : spatialADMPartial l (fun y => h y i j) x = spatialADMPartial l (fun y => h y j i) x := sym_h hw hp hx l i j
    rw [e,add_comm (spatialADMPartial i _ _) _]
  have hsym (i j : I) : H i j=H j i := by
    change pd i (pd j u) x - (∑ a : I, G a i j*n a) = pd j (pd i u) x - (∑ a : I, G a j i*n a)
    rw [d_sym cn i j]
    simp_rw [gs _ i j]
  have low (y : X) (wy : y∈W) (i : I) : (∑ a : I, h y i a * q a y) = p i y := by
    let n' := fun t => pd t u y
    have B : ((h y) *ᵥ ((h y)⁻¹ *ᵥ n')) i = n' i := by
      rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ ((h y).isUnit_iff_isUnit_det.mp (hp y wy).isUnit),Matrix.one_mulVec]
    have low' : ∑ a : I, h y i a * staticRaisedGradient u h a y = pd i u y := B
    change (∑ a : I, h y i a * (z y * staticRaisedGradient u h a y)) = z y*pd i u y
    rw [←low']
    simp only [Fin.sum_univ_three]; ring
  have trx (y : X) (wy : y∈W) (i : I) : (∑ a : I, C y a a i) = 3*p i y := by
    have s (a : I) : h y a i = h y i a := by simpa only [star_trivial] using (hp y wy).isHermitian.apply i a
    calc
      _ = (∑ _a : I, p i y) + (∑ a : I, kr a i*p a y) - (∑ a : I, h y i a*q a y) := by
        simp only [C,connectionChange,show ∀ a : I, kr a a = 1 by simp [kr],one_mul,s,Finset.sum_sub_distrib,Finset.sum_add_distrib]
      _ = _ := by rw [deltaSum i (fun a => p a y),low y wy i]; simp [Fin.sum_univ_three] <;> ring
  have dznear : ∀ᶠ y in 𝓝 x, u y≠0 := cn.continuousAt.tendsto (isOpen_compl_singleton.mem_nhds hn)
  have changeAt (y : X) (wy : y∈W) (ny : u y≠0) (a i j : I) :
      spatialLeviCivita k y a i j = spatialLeviCivita h y a i j + C y a i j := by
    have e := (spatial_conformal_connection u h W hw hu hh hp y wy ny).2 a i j
    change spatialLeviCivita k y a i j = spatialLeviCivita h y a i j + kr a i*p j y + kr a j*p i y - h y i j*q a y at e
    rw [e]
    dsimp only [C,connectionChange]; ring
  have dG (t a i j : I) : spatialADMPartial t (fun y => spatialLeviCivita k y a i j) x =
      spatialADMPartial t (fun y => spatialLeviCivita h y a i j) x + pd t (fun y => C y a i j) x := by
    have ev : (fun y => spatialLeviCivita k y a i j) =ᶠ[𝓝 x] (fun y => spatialLeviCivita h y a i j+C y a i j) := by
      filter_upwards [hw.mem_nhds hx,dznear] with y wy ny
      exact changeAt y wy ny a i j
    exact (congrArg (fun D : X →L[ℝ] ℝ => D (bvec t)) ev.fderiv_eq).trans
      (d_add ((sm_ch (hp x hx) ch a i j).differentiableAt (by simp)) ((cc a i j).differentiableAt (by simp)) t)
  have trD (j i : I) : (∑ a : I, pd j (fun y => C y a a i) x) = 3 * dp j i := by
    have ev : (fun y => ∑ a : I, C y a a i) =ᶠ[𝓝 x] (fun y => 3*p i y) :=
      (show ∀ᶠ y in 𝓝 x, y∈W from hw.mem_nhds hx).mono fun y wy => trx y wy i
    rw [←pd_sum (f:=fun a y => C y a a i) (fun a => (cc a a i).differentiableAt (by simp)) j]
    exact (congrArg (fun D : X →L[ℝ] ℝ => D (bvec j)) ev.fderiv_eq).trans (d_cmul ((cp i).differentiableAt (by simp)) 3 j)
  have dC (t a i j : I) : pd t (fun y => C y a i j) x =
      kr a i*dp t j + kr a j*dp t i - (pd t (fun y => h y i j) x*Q a+h x i j*dq t a) := by
    have df := (cp j).differentiableAt (by simp)
    have dg := (cp i).differentiableAt (by simp)
    change pd t (fun y => kr a i*p j y + kr a j*p i y - h y i j*q a y) x = _
    rw [d_sub (f:=fun y => kr a i*p j y + kr a j*p i y) (g:=fun y => h y i j*q a y)
      ((df.const_mul (kr a i)).add (dg.const_mul (kr a j))) (((ch i j).mul (cq a)).differentiableAt (by simp)) t,
      d_add (f:=fun y => kr a i*p j y) (g:=fun y => kr a j*p i y)
        (df.const_mul (kr a i)) (dg.const_mul (kr a j)) t,
      d_cmul (f:=p j) df (kr a i) t,d_cmul (f:=p i) dg (kr a j) t,
      pd_mul (f:=fun y => h y i j) (g:=q a) ((ch i j).differentiableAt (by simp)) ((cq a).differentiableAt (by simp)) t]
  have dcSum (i j : I) : (∑ a : I, pd a (fun y => C y a j i) x) = dp j i + dp i j -
      (∑ a : I, pd a (fun y => h y j i) x*Q a) - h x j i * (∑ a : I, dq a a) := calc
    _ = (∑ a : I, kr a j*dp a i) + (∑ a : I, kr a i*dp a j) -
      (∑ a : I, pd a (fun y => h y j i) x*Q a) - h x j i * (∑ a : I, dq a a) := by
        simp only [dC,Fin.sum_univ_three]; ring
    _ = _ := by rw [deltaSum j (fun a => dp a i),deltaSum i (fun a => dp a j)]
  have raw (i j : I) : spatialRicciTensor k x i j = spatialRicciTensor h x i j +
      (∑ a : I, pd a (fun y => C y a j i) x) - (∑ a : I, pd j (fun y => C y a a i) x) +
      mixed G (C x) i j + quadratic (C x) i j := by
    have gp : spatialLeviCivita k x = fun a r l => G a r l + C x a r l :=
      funext fun a => funext fun r => funext fun l => changeAt x hx hn a r l
    simp only [ricci_parts,dG,gp,quadratic_add,Finset.sum_add_distrib,G]
    ring
  let cov := fun i j => dp i j - ∑ a : I, G a i j*P a
  let div := ∑ a : I, (dq a a + ∑ l : I, G a a l*Q l)
  have ric0 (i j : I) : spatialRicciTensor k x i j = spatialRicciTensor h x i j +
      cov i j - 2*cov j i - h x j i*div + P i*P j - h x j i*(∑ a : I, P a*Q a) := by
    have lo (a : I) : P a=∑ l : I, h x a l*Q l := (low x hx a).symm
    have lin : mixed G (C x) i j =
        (∑ a : I, ((∑ l : I, h x j l*G l a i)+(∑ l : I, h x l i*G l a j))*Q a) +
        (∑ l : I, G l j i * P l) - h x j i*(∑ a : I, ∑ l : I, G a a l*Q l) := mixed_contraction (h x) G P Q sym gs lo i j
    have sq : quadratic (C x) i j = P i*P j - h x j i*(∑ a : I, P a*Q a) := quadratic_contraction (h x) P Q sym lo i j
    have dh (a : I) : pd a (fun y => h y j i) x =
        (∑ l : I, h x j l*G l a i)+(∑ l : I, h x l i*G l a j) := metric_comp hw hp hx a j i
    rw [raw,dcSum,trD,lin,sq]
    simp only [dh,cov,div,gs _ i j,Finset.sum_add_distrib]
    ring
  have zder (i : I) : pd i z x=-(2/u x^2)*n i := by
    have ev : (fun y => z y * u y) =ᶠ[𝓝 x] (fun _ => 2) := dznear.mono fun y ny => div_mul_cancel₀ _ ny
    have zero : pd i (fun _ : X => (2:ℝ)) x = 0 := by simp [pd,spatialADMPartial]
    have a := (congrArg (fun D : X →L[ℝ] ℝ => D (bvec i)) ev.fderiv_eq).trans zero
    change pd i (fun y => z y * u y) x = 0 at a
    rw [pd_mul (f:=z) (g:=u) (cz.differentiableAt (by simp)) (cn.differentiableAt (by simp)) i] at a
    change pd i z x * u x + (2/u x)*n i = 0 at a
    field_simp [hn] at a ⊢
    linear_combination a
  have covVal (i j : I) : cov i j= z x*H i j - (2/u x^2)*n i*n j := by
    have dv : dp i j = pd i z x*n j + z x*pd i (pd j u) x :=
      pd_mul (f:=z) (g:=pd j u) (cz.differentiableAt (by simp)) ((sm_pd cn j).differentiableAt (by simp)) i
    simp only [cov,dv,zder,H,staticSpatialHessian,P,p,n,G,pd,Fin.sum_univ_three]
    ring
  have divVal : div = z x*L - (2/u x^2)*E := by
    have row (i : I) : dq i i + (∑ l : I, G i i l*Q l) =
        z x*(∑ j : I, (h x)⁻¹ i j * H i j) - (2/u x^2)*n i*staticRaisedGradient u h i x := by
      have d : dq i i = pd i z x*staticRaisedGradient u h i x + z x*pd i (staticRaisedGradient u h i) x :=
        pd_mul (f:=z) (g:=staticRaisedGradient u h i) (cz.differentiableAt (by simp))
          ((sm_grad (hp x hx) ch cn i).differentiableAt (by simp)) i
      have eq := (static_lapse_gradient_covariant_derivative u h W hw hu hh hp x hx i).1 i
      change pd i (staticRaisedGradient u h i) x + (∑ l : I, G i i l*staticRaisedGradient u h l x) =
        ∑ j : I, (h x)⁻¹ i j * H i j at eq
      rw [←eq,d,zder]
      simp only [Q,q,Fin.sum_univ_three]; ring
    dsimp only [div]
    simp_rw [row]
    simp only [L,E,staticLapseGradientSq,n,pd,Fin.sum_univ_three]; ring
  have eVal : (∑ a : I, P a*Q a) = (z x)^2*E := by
    simp only [P,Q,p,q,E,staticLapseGradientSq,pd,Fin.sum_univ_three]; ring
  intro i j
  change spatialRicciTensor k x i j = _
  rw [ric0,covVal,covVal,divVal,eVal,hsym j i,sym j i]
  change _ = spatialRicciTensor h x i j - (2/u x)*H i j - (2/u x)*h x i j*L + (6/u x^2)*n i*n j - (2/u x^2)*h x i j*E
  simp only [P,p,z,n,pd]
  field_simp [hn] <;> ring
