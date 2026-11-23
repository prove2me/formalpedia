-- Prove2me | solution 1 for NoHair.euclidean_riemannian_cover_deck_isometries_transitive
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:08:39.530978+00:00
-- url     : https://prove2.me/submissions/fc474c3c-4f30-4968-8951-0c7a486415ff

import Definitions.Def_NoHair_spatialRiemannCurvature
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Geometry.Manifold.Instances.Icc

open NoHair Set Filter Bundle
open scoped Topology ContDiff Manifold

noncomputable section

open Manifold MeasureTheory
open scoped ENNReal NNReal
private abbrev X := ADMPoint
private abbrev I := 𝓘(ℝ,X)

private lemma smooth_lift {Q E H A : Type} [MetricSpace Q] [ChartedSpace X Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [TopologicalSpace A] [ChartedSpace H A]
    {J : ModelWithCorners ℝ E H} {p : X → Q} {f : A → Q} {lift : A → X}
    {n : ℕ∞ω} (dif : IsLocalDiffeomorph I I n p) (cf : ContMDiff J I n f)
    (cl : Continuous lift) (eq : p ∘ lift = f) : ContMDiff J I n lift := by
  intro t
  obtain ⟨φ,src,agrees⟩ := dif (lift t)
  have atSource : ∀ᶠ s in 𝓝 t, lift s ∈ φ.source := cl.continuousAt (φ.open_source.mem_nhds src)
  have id (s : A) (hs : lift s ∈ φ.source) : f s=φ (lift s) :=
    (congrFun eq s).symm.trans (agrees hs)
  have loc : lift =ᶠ[𝓝 t] (φ.toPartialEquiv.symm ∘ f) :=
    atSource.mono fun s hs => by simp only [Function.comp_apply,id s hs,φ.left_inv hs]
  have mem : f t ∈ φ.target := (id t src) ▸ φ.map_source src
  have ci := φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds mem)
  exact (ci.comp t (cf t)).congr_of_eventuallyEq loc

private lemma norm_push {Q : Type} [MetricSpace Q] [ChartedSpace X Q] [IsManifold I ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace I q)] {p : X → Q}
    (iso : ∀ x v w : X, inner ℝ (mfderiv I I p x v) (mfderiv I I p x w) = inner ℝ v w)
    (x v : X) : ‖mfderiv I I p x v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using iso x v v

set_option backward.isDefEq.respectTransparency false in
theorem solution (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [ConnectedSpace Q] (p : ADMPoint → Q)
    (cov : IsCoveringMap p) (dif : IsLocalDiffeomorph 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ p)
    (iso : ∀ x v w : ADMPoint, inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x v)
      (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x w) = inner ℝ v w) :
    ∀ x y, p x=p y → ∃ γ : ADMPoint ≃ᵢ ADMPoint, γ x=y ∧ ∀ z, p (γ z)=p z := by
  classical
  have cp := dif.contMDiff
  let projC : C(X,Q) := ⟨p,cov.continuous⟩
  have short (f : C(X,X)) (ef : p ∘ f=p) : LipschitzWith 1 f := by
    have smooth := smooth_lift dif cp f.continuous ef
    have cf := contMDiff_iff_contDiff.mp smooth
    apply lipschitzWith_of_nnnorm_fderiv_le (cf.differentiable (by simp))
    intro z
    change ‖fderiv ℝ f z‖ ≤ 1
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    have push := congrArg (fun g : X → Q => ‖mfderiv I I g z v‖) ef
    have comp := mfderiv_comp (I':=I) z ((dif (f z)).mdifferentiableAt (by simp))
      (smooth.contMDiffAt.mdifferentiableAt (by simp))
    have hh := congrArg (fun L : X →L[ℝ] TangentSpace I (p (f z)) => ‖L v‖) comp
    change ‖mfderiv I I (p ∘ f) z v‖ = ‖mfderiv I I p (f z) (mfderiv I I f z v)‖ at hh
    have final := ((norm_push iso (f z) (mfderiv I I f z v)).symm.trans hh.symm).trans (push.trans (norm_push iso z v))
    have changeD : (mfderiv I I f z : X →L[ℝ] X) = fderiv ℝ (f : X → X) z := mfderiv_eq_fderiv
    have point := congrArg (fun L : X →L[ℝ] X => ‖L v‖) changeD.symm
    rw [one_mul]
    exact (point.trans final).le
  intro x y xy
  obtain ⟨f,⟨fx,fp⟩,_⟩ := cov.existsUnique_continuousMap_lifts projC x y xy.symm
  obtain ⟨g,⟨gy,gp⟩,_⟩ := cov.existsUnique_continuousMap_lifts projC y x xy
  have fp' : p ∘ f=p := fp
  have gp' : p ∘ g=p := gp
  have inv {a b:X} {F G : C(X,X)} (fa : F a=b) (gb : G b=a)
      (hf : p ∘ F=p) (hg : p ∘ G=p) : Function.LeftInverse G F := by
    have e : p ∘ (G ∘ F) = p ∘ id := by rw [←Function.comp_assoc,hg,hf,Function.comp_id]
    have z := cov.eq_of_comp_eq (G.continuous.comp F.continuous) continuous_id e a (by simp [fa,gb])
    exact fun w => congrFun z w
  have l := inv fx gy fp' gp'
  have r := inv gy fx gp' fp'
  have fl := short f fp'
  have gl := short g gp'
  have fi : Isometry f := by
    intro a b
    apply le_antisymm
    · simpa only [ENNReal.coe_one,one_mul] using fl a b
    · have z := gl (f a) (f b)
      simpa only [l a,l b,ENNReal.coe_one,one_mul] using z
  exact ⟨⟨⟨f,g,l,r⟩,fi⟩,fx,fun z => congrFun fp' z⟩
