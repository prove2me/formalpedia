-- Prove2me | solution 1 for NoHair.regular_static_horizon_surface_gravity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:28:53.063717+00:00
-- url     : https://prove2.me/submissions/05f9e28a-5ebd-4c36-bd8a-3290c9ec512e

import Theorems.Thm_NoHair_static_lapse_gradient_covariant_derivative
import Theorems.Thm_NoHair_constant_on_connected_regular_level
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

private lemma zero_on_frame {A : X →L[ℝ] ℝ} (ha : ∀ i : I, A (bvec i)=0) : A=0 := by
  apply ContinuousLinearMap.ext
  intro y
  have eq := congrArg (fun z : X => A z) ((EuclideanSpace.basisFun I ℝ).sum_repr y)
  simp only [map_sum,map_smul,EuclideanSpace.basisFun_apply] at eq
  rw [← eq]
  simp only [ha,smul_zero,Finset.sum_const_zero,ContinuousLinearMap.zero_apply]

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) (heq : StaticSliceEquations c.Ω c.N c.h) :
    StaticHorizonGeometry c.Ω c.N c.h := by
  classical
  let E := staticLapseGradientSq c.N c.h
  let S := frontier c.Ω
  have sub : S ⊆ c.W := frontier_subset_closure.trans c.extendsAcross
  have cn {x : X} (hx : x∈c.W) := c.smoothLapse.contDiffAt (c.openExtension.mem_nhds hx)
  have ch {x : X} (hx : x∈c.W) (i j : I) := (c.smoothMetric i j).contDiffAt (c.openExtension.mem_nhds hx)
  have ce {x : X} (hx : x∈c.W) : ContDiffAt ℝ ∞ E x := ContDiffAt.sum fun i _ =>
    (sm_pd (cn hx) i).mul (sm_grad (c.positiveMetric x hx) (ch hx) (cn hx) i)
  have hz (x : X) (hx : x∈S) (i j : I) : staticSpatialHessian c.N c.h i j x=0 := by
    rw [(heq x (frontier_subset_closure hx)).1 i j,(c.horizon x hx).1,zero_mul]
  have de (x : X) (hx : x ∈ S) : fderiv ℝ E x=0 := by
    apply zero_on_frame
    intro i
    have d := (static_lapse_gradient_covariant_derivative c.N c.h c.W c.openExtension c.smoothLapse
      c.smoothMetric c.positiveMetric x (sub hx) i).2
    change spatialADMPartial i (staticLapseGradientSq c.N c.h) x = 0
    simpa only [hz x hx,zero_mul,Finset.sum_const_zero,mul_zero] using d
  have pos (x : X) (hx : x∈S) : 0<E x := by
    let n := fun i : I => pd i c.N x
    have n0 : n ≠ 0 := by
      intro h
      exact (c.horizon x hx).2 (zero_on_frame (fun i => congrFun h i))
    have d := (c.positiveMetric x (sub hx)).inv.dotProduct_mulVec_pos n0
    change 0 < dotProduct n ((c.h x)⁻¹ *ᵥ n)
    simpa only [star_trivial] using d
  have classLevel (x : X) (hx : x∈S) : ∀ᶠ y in 𝓝 x, y ∈ S ↔ c.N y=0 := by
    have d := (cn (sub hx)).continuousAt_fderiv (by simp)
    have nz : ∀ᶠ y in 𝓝 x, fderiv ℝ c.N y ≠ 0 := d.tendsto
      (isOpen_compl_singleton.mem_nhds (show fderiv ℝ c.N x ∈ ({0}ᶜ : Set (X →L[ℝ] ℝ)) from (c.horizon x hx).2))
    filter_upwards [nz,c.openExtension.mem_nhds (sub hx)] with y ny wy
    refine ⟨fun h => (c.horizon y h).1,?_⟩
    intro zero
    have outside : y ∉ c.Ω := fun h => by simpa [zero] using (c.positiveSide y wy).mp h
    rw [show S = closure c.Ω \ c.Ω from c.openSlice.frontier_eq]
    refine ⟨?_,outside⟩
    by_contra far
    have maximum : IsLocalMax c.N y := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds far,c.openExtension.mem_nhds wy] with u faru wu
      rw [zero]
      exact le_of_not_gt (fun up => faru (subset_closure ((c.positiveSide u wu).mpr up)))
    exact ny maximum.fderiv_eq_zero
  obtain ⟨p,hp⟩ := c.hasBoundary
  have eq := constant_on_connected_regular_level c.W S c.N E c.connectedBoundary c.openExtension sub
    (c.smoothLapse.of_le (by simp)) (fun y hy => ((ce hy).differentiableAt (by simp)).differentiableWithinAt)
    (fun y hy => (c.horizon y hy).2) classLevel de
  refine ⟨Real.sqrt (E p),Real.sqrt_pos.mpr (pos p hp),?_⟩
  intro x hx
  exact ⟨hz x hx,(eq x hx p hp).trans (Real.sq_sqrt (pos p hp).le).symm,de x hx⟩
