-- Prove2me | solution 1 for NoHair.static_conformal_halves_signed_lapse_equation
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:34:57.590673+00:00
-- url     : https://prove2.me/submissions/0e820f76-12f7-4142-aee3-40881c639195

import Theorems.Thm_NoHair_spatial_laplacian_in_divergence_form
import Theorems.Thm_NoHair_static_conformal_halves_nondegenerate
import Theorems.Thm_NoHair_spatial_conformal_connection
import Definitions.Def_NoHair_staticConformalCompletion

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

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∀ x ∈ closure Ω, ∀ s : ℝ, s=1 ∨ s=-1 →
      staticWeightedLapseDivergence (staticPositiveMetric (fun y => s*N y) h) (fun y => s*N y) x = 0 := by
  classical
  intro x hx s hs
  let f := fun y => s*N y
  let u := fun y => (1+f y)/2
  let k : X → Mat := staticPositiveMetric f h
  have cn {y : X} (wy : y∈W) := c.smoothLapse.contDiffAt (c.openExtension.mem_nhds wy)
  have cu : ContDiffOn ℝ ∞ u W :=
    ((contDiffOn_const.add (contDiffOn_const.mul c.smoothLapse)).mul contDiffOn_const : ContDiffOn ℝ ∞
      (fun y => (1+s*N y)*(2:ℝ)⁻¹) W)
  have wx := c.extendsAcross hx
  have range := static_conformal_halves_nondegenerate Ω W N h c x hx
  have uv : 0<u x := by
    apply half_pos
    dsimp only [f]
    rcases hs with e|e <;> rw [e] <;> nlinarith only [range.1,range.2.1]
  have nu : ∀ᶠ y in 𝓝 x, 0<u y := (cu.contDiffAt (c.openExtension.mem_nhds wx)).continuousAt.tendsto
    (isOpen_Ioi.mem_nhds uv)
  let A := fun (i : I) (y : X) => Real.sqrt (h y).det * staticRaisedGradient N h i y
  let D := fun (i : I) (y : X) => Real.sqrt (k y).det * (2/(1+f y))^2 *
    (∑ j : I, (k y)⁻¹ i j * spatialADMPartial j f y)
  have weighted (y : X) (wy : y∈W) (uy : 0<u y) (i : I) : D i y=s*A i y := by
    have sc : k y=(u y)^4 • h y := rfl
    have iv := (spatial_conformal_connection u h W c.openExtension cu c.smoothMetric c.positiveMetric y wy uy.ne').1
    have kiv (j : I) : (k y)⁻¹ i j = (u y^4)⁻¹*(h y)⁻¹ i j := congrArg (fun m : Mat => m i j) iv
    have root : Real.sqrt (k y).det = u y^6 * Real.sqrt (h y).det := by
      rw [sc,Matrix.det_smul]
      have P : (u y ^4)^Fintype.card (Fin 3) = (u y^6)^2 := by norm_num [←pow_mul]
      rw [P,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (pow_nonneg uy.le 6)]
    have df (j : I) : spatialADMPartial j f y=s*spatialADMPartial j N y := by
      have q := (((cn wy).differentiableAt (by simp)).hasFDerivAt.const_mul s).fderiv
      change fderiv ℝ f y = _ at q
      unfold spatialADMPartial
      rw [q]; rfl
    have weight : 2/(1+f y) = (u y)⁻¹ := by simp only [u,inv_div]
    dsimp only [D,A]
    simp only [root,kiv,weight,df,staticRaisedGradient,Fin.sum_univ_three]
    field_simp [uy.ne'] <;> ring
  have deriv (i : I) : spatialADMPartial i (D i) x = s*spatialADMPartial i (A i) x := by
    have ev : D i =ᶠ[𝓝 x] (fun y => s*A i y) := by
      filter_upwards [nu,c.openExtension.mem_nhds wx] with y uy wy
      exact weighted y wy uy i
    have sd : ContDiffAt ℝ ∞ (fun y => (h y).det) x := by
      simp_rw [Matrix.det_fin_three]
      have ch (a b : I) := (c.smoothMetric a b).contDiffAt (c.openExtension.mem_nhds wx)
      fun_prop
    have grad : DifferentiableAt ℝ (staticRaisedGradient N h i) x := by
      have nn := (cn wx).differentiableAt (by simp)
      have car (a b : I) := (c.smoothMetric a b).contDiffAt (c.openExtension.mem_nhds wx)
      exact (sm_grad (c.positiveMetric x wx) car (cn wx) i).differentiableAt (by simp)
    have da : DifferentiableAt ℝ (A i) x := ((Real.hasDerivAt_sqrt (c.positiveMetric x wx).det_pos.ne').comp_hasFDerivAt x
      (sd.differentiableAt (by simp)).hasFDerivAt).differentiableAt.mul grad
    let bvec := EuclideanSpace.single i (1:ℝ)
    calc
      _ = spatialADMPartial i (fun y => s*A i y) x := congrArg (fun L : X →L[ℝ] ℝ => L bvec) ev.fderiv_eq
      _ = _ := by unfold spatialADMPartial; rw [(da.hasFDerivAt.const_mul s).fderiv]; rfl
  have hdiv := spatial_laplacian_in_divergence_form N h W c.openExtension c.smoothLapse c.smoothMetric c.positiveMetric x wx
  change (∑ i : I, spatialADMPartial i (A i) x) = _ at hdiv
  change (∑ i : I, spatialADMPartial i (D i) x)=0
  simp only [deriv,←Finset.mul_sum,hdiv,(c.equations x hx).2,mul_zero]
