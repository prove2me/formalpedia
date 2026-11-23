-- Prove2me | solution 1 for NoHair.ricci_flat_atlas_has_zero_riemann_curvature
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:09:48.240737+00:00
-- url     : https://prove2.me/submissions/7b300d0a-14a5-4140-99c0-963ee9ca7b69

import Theorems.Thm_NoHair_spatial_ricci_flat_implies_riemann_flat_three
import Definitions.Def_NoHair_spatialRiemannCurvature

open NoHair Set Filter Bundle
open scoped Topology ContDiff Manifold

noncomputable section

open IsManifold ChartedSpace Manifold
open scoped Bundle
private abbrev X := ADMPoint
private noncomputable abbrev I := 𝓘(ℝ,X)
private noncomputable abbrev b (i : Fin 3) : X := EuclideanSpace.single i 1
set_option backward.isDefEq.respectTransparency false in
theorem solution (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    (ric : RicciFlatInADMCharts Q) : FlatInADMCharts Q := by
  intro e he x hx
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
  exact spatial_ricci_flat_implies_riemann_flat_three e.target e.open_target _ smooth pos x hx (ric e he x hx)
