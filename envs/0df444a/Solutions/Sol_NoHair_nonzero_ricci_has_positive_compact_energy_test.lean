-- Prove2me | solution 1 for NoHair.nonzero_ricci_has_positive_compact_energy_test
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:36:14.795858+00:00
-- url     : https://prove2.me/submissions/65e8ca59-4045-431d-986b-d9a58310b136

import Definitions.Def_NoHair_spatialRicciEnergyDensity

open NoHair Set Filter Bundle MeasureTheory
open scoped ContDiff Manifold Topology

noncomputable section

open IsManifold ChartedSpace Manifold
open scoped Bundle
private abbrev X := ADMPoint
private noncomputable abbrev I := 𝓘(ℝ,X)
private noncomputable abbrev b (i : Fin 3) : X := EuclideanSpace.single i 1
open Metric Matrix
open scoped Matrix Kronecker
private abbrev Idx := Fin 3
private abbrev Mat := Matrix Idx Idx ℝ
private noncomputable abbrev pd := spatialADMPartial
private noncomputable abbrev bvec (i : Idx) : X := EuclideanSpace.single i 1

private lemma sm_pd {f : X → ℝ} {x : X} (c : ContDiffAt ℝ ∞ f x) (i : Idx) :
    ContDiffAt ℝ ∞ (pd i f) x :=
  (c.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

private lemma sm_inv {h : X → Mat} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (a b : Idx) :
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
  exact ((detS (ι:=Idx) h hc).inv det0).mul adj

private lemma sm_ch {h : X → Mat} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (a i j : Idx) :
    ContDiffAt ℝ ∞ (fun y => spatialLeviCivita h y a i j) x :=
  contDiffAt_const.mul (ContDiffAt.sum fun l _ => (sm_inv hp hc a l).mul
    (((sm_pd (hc l j) i).add (sm_pd (hc l i) j)).sub (sm_pd (hc i j) l)))

set_option backward.isDefEq.respectTransparency false in
theorem solution (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    (hric : ¬ RicciFlatInADMCharts Q) :
    ∃ (e : OpenPartialHomeomorph Q ADMPoint), e∈atlas ADMPoint Q ∧ ∃ χ : ADMPoint → ℝ, 0 ≤ χ ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ e.target ∧
      0 < ∫ x : ADMPoint, χ x*spatialRicciEnergyDensity (riemannianEndCoeffs e.symm) x := by
  classical
  unfold RicciFlatInADMCharts at hric
  push_neg at hric
  obtain ⟨e,he,x,hx,i,j,nz⟩ := hric
  have atlasE : e ∈ maximalAtlas I ∞ Q := IsManifold.subset_maximalAtlas he
  have invs : ContMDiffOn I I ∞ e.symm e.target := contMDiffOn_symm_of_mem_maximalAtlas atlasE
  have vec (i : Fin 3) : ContMDiffOn I I.tangent ∞ (fun z : X =>
      (⟨e.symm z,mfderiv I I e.symm z (b i)⟩ : TangentBundle I Q)) e.target := by
    let sec := fun z : X => (⟨z,b i⟩ : TangentBundle I X)
    have smoothSec : ContMDiff I I.tangent ∞ sec :=
      (contMDiff_vectorSpace_iff_contDiff (V:=fun _ : X => b i)).mpr contDiff_const
    have t := invs.contMDiffOn_tangentMapWithin (m:=∞) (by simp) e.open_target.uniqueMDiffOn
    have comp := t.comp smoothSec.contMDiffOn (show MapsTo sec e.target _ from fun _ hz => hz)
    apply comp.congr
    intro y hy
    change (⟨e.symm y, mfderiv I I e.symm y (b i)⟩ : TangentBundle I Q) =
      ⟨e.symm y,mfderivWithin I I e.symm e.target y (b i)⟩
    rw [mfderivWithin_of_mem_nhds (e.open_target.mem_nhds hy)]
  have smooth (a b : Fin 3) : ContDiffOn ℝ ∞ (fun z => riemannianEndCoeffs e.symm z a b) e.target := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact (vec a).inner_bundle (vec b)
  have pos (y : X) (hy : y∈e.target) : (riemannianEndCoeffs e.symm y).PosDef := by
    let D := mfderiv I I e.symm y
    have ci := (contMDiffAt_symm_of_mem_maximalAtlas atlasE hy).mdifferentiableAt (by simp : (∞:ℕ∞ω) ≠ 0)
    have ce := (contMDiffAt_of_mem_maximalAtlas atlasE (e.map_target hy)).mdifferentiableAt (by simp : (∞:ℕ∞ω) ≠ 0)
    have eq := mfderiv_comp (I':=I) y ce ci
    have loc : (e ∘ e.symm) =ᶠ[𝓝 y] id :=
      (show ∀ᶠ z in 𝓝 y, z∈e.target from e.open_target.mem_nhds hy).mono (fun z hz => e.right_inv hz)
    change mfderiv I I (e ∘ e.symm) y = (mfderiv I I e (e.symm y)).comp D at eq
    rw [mfderiv_eq_fderiv,loc.fderiv_eq,fderiv_id] at eq
    have left (v : X) : mfderiv I I e (e.symm y) (D v) = v := congrArg (fun L : X →L[ℝ] X => L v) eq.symm
    have inj : Function.Injective D := fun v w h => (left v).symm.trans ((congrArg _ h).trans (left w))
    change (Matrix.gram ℝ (fun i => D (b i))).PosDef
    apply Matrix.posDef_gram_of_linearIndependent
    have li := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.linearIndependent.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr inj)
    rw [Fintype.linearIndependent_iff] at li ⊢
    intro a ha
    apply li a
    simp only [Function.comp_def,OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,b,D,Fin.sum_univ_three,ContinuousLinearMap.coe_coe] at ha ⊢
    first | exact ha | convert! ha using 1 <;> rfl'
  let h := riemannianEndCoeffs e.symm
  have reg (y:X) (hy:y∈e.target) (a b:Idx) : ContDiffAt ℝ ∞ (fun z => spatialRicciTensor h z a b) y := by
    have ch (m n:Idx) : ContDiffAt ℝ ∞ (fun z => h z m n) y := (smooth m n).contDiffAt (e.open_target.mem_nhds hy)
    have cc (i j k:Idx) := sm_ch (pos y hy) ch i j k
    exact ContDiffAt.sum fun t _ => ((sm_pd (cc t b a) t).sub (sm_pd (cc t t a) b)).add
      (ContDiffAt.sum fun l _ => ((cc t t l).mul (cc l b a)).sub ((cc t b l).mul (cc l t a)))
  let ρ := spatialRicciEnergyDensity h
  have density (y:X) (hy:y∈e.target) : ContinuousAt ρ y := by
    have ch (m n:Idx) : ContDiffAt ℝ ∞ (fun z => h z m n) y := (smooth m n).contDiffAt (e.open_target.mem_nhds hy)
    have det : ContinuousAt (fun z => (h z).det) y := by
      simp only [Matrix.det_fin_three]
      fun_prop (disch := exact (ch _ _).continuousAt)
    have iv (i j:Idx) := sm_inv (pos y hy) ch i j
    have hs : ContDiffAt ℝ ∞ (fun z => ∑ v : Idx × Idx, spatialRicciTensor h z v.1 v.2 *
        (∑ w : Idx × Idx, ((h z)⁻¹ v.1 w.1 * (h z)⁻¹ v.2 w.2) * spatialRicciTensor h z w.1 w.2)) y :=
      ContDiffAt.sum fun v _ => (reg y hy v.1 v.2).mul (ContDiffAt.sum fun w _ =>
        ((iv v.1 w.1).mul (iv v.2 w.2)).mul (reg y hy w.1 w.2))
    exact det.sqrt.mul hs.continuousAt
  have val (y:X) : ρ y = Real.sqrt (h y).det * dotProduct
    (fun a : Idx × Idx => spatialRicciTensor h y a.1 a.2)
    (((h y)⁻¹ ⊗ₖ (h y)⁻¹) *ᵥ (fun a : Idx × Idx => spatialRicciTensor h y a.1 a.2)) := rfl
  have non (y:X) (hy:y∈e.target) : 0≤ρ y := by
    rw [val]
    apply mul_nonneg (Real.sqrt_nonneg _)
    have ip := (pos y hy).inv
    simpa only [star_trivial] using (ip.kronecker ip).posSemidef.dotProduct_mulVec_nonneg
      (fun a : Idx × Idx => spatialRicciTensor h y a.1 a.2)
  have positive : 0<ρ x := by
    rw [val]
    apply mul_pos (Real.sqrt_pos.mpr (pos x hx).det_pos)
    have ip := (pos x hx).inv
    have nv : (fun a : Idx × Idx => spatialRicciTensor h x a.1 a.2)≠0 := by
      intro z; exact nz (congrFun z (i,j))
    simpa only [star_trivial] using (ip.kronecker ip).dotProduct_mulVec_pos nv
  obtain ⟨r,rp,inside⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hx)
  let χ : ContDiffBump x := ⟨r/4,r/2,by linarith,by linarith⟩
  have sub : tsupport χ ⊆ e.target := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show χ.rOut<r by change r/2<r; linarith)).trans inside
  let g := fun z : X => χ z*ρ z
  have zero {y:X} (ny : y∉tsupport χ) : χ y=0 := by
    by_contra bad
    exact ny (subset_closure (show y∈Function.support χ from bad))
  have cg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy:y∈e.target
    · exact (show ContDiff ℝ ∞ (χ : X → ℝ) from χ.contDiff).continuous.continuousAt.mul (density y hy)
    · have ns : y∉tsupport χ := fun z => hy (sub z)
      apply (continuousAt_const : ContinuousAt (fun _ : X => (0:ℝ)) y).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (χ : X → ℝ)).isOpen_compl.mem_nhds ns] with z hz
      simp only [g,zero hz,zero_mul]
  have gn (y:X) : 0≤g y := by
    by_cases hy:y∈e.target
    · exact mul_nonneg (χ.nonneg) (non y hy)
    · simp only [g,zero (fun z => hy (sub z)),zero_mul,le_rfl]
  have gx : 0<g x := by simp only [g,χ.one_of_mem_closedBall (mem_closedBall_self χ.rIn_pos.le),one_mul]; exact positive
  refine ⟨e,he,χ,fun y => χ.nonneg,χ.contDiff,χ.hasCompactSupport,sub,?_⟩
  exact cg.integral_pos_of_hasCompactSupport_nonneg_nonzero (χ.hasCompactSupport.mul_right (f':=ρ)) gn gx.ne'
