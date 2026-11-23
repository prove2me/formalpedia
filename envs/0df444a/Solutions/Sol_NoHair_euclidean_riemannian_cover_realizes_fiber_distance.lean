-- Prove2me | solution 1 for NoHair.euclidean_riemannian_cover_realizes_fiber_distance
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:08:21.916261+00:00
-- url     : https://prove2.me/submissions/df635904-9b35-4be1-930f-30baf4f517c7

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

theorem solution (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [ConnectedSpace Q] (p : ADMPoint → Q)
    (cov : IsCoveringMap p) (dif : IsLocalDiffeomorph 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ p)
    (iso : ∀ x v w : ADMPoint, inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x v)
      (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x w) = inner ℝ v w) :
    ∀ x : ADMPoint, ∀ q : Q, ∃ y : ADMPoint, p y=q ∧ dist x y=dist (p x) q := by
  classical
  letI : LocallyPathConnectedSpace Q := ChartedSpace.locallyPathConnectedSpace X Q
  letI : PathConnectedSpace Q := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  have cp : ContMDiff I I 1 p := (dif.contMDiff).of_le (by simp)
  have df : IsLocalDiffeomorph I I 1 p := by
    intro x
    obtain ⟨φ,hx,eq⟩ := dif x
    let φ' : PartialDiffeomorph I I X Q 1 := ⟨φ.toPartialEquiv,φ.open_source,φ.open_target,
      φ.contMDiffOn_toFun.of_le (by simp),φ.contMDiffOn_invFun.of_le (by simp)⟩
    exact ⟨φ',hx,eq⟩
  have energy {a b : X} (γ : Path a b) (cg : ContMDiff (𝓡∂ 1) I 1 γ) (t : unitInterval) :
      ‖(mfderiv (𝓡∂ 1) I (p ∘ γ) t) 1‖ₑ = ‖(mfderiv (𝓡∂ 1) I γ t) 1‖ₑ := by
    rw [mfderiv_comp (I':=I) t (cp.contMDiffAt.mdifferentiableAt one_ne_zero)
      (cg.contMDiffAt.mdifferentiableAt one_ne_zero),ContinuousLinearMap.comp_apply]
    let v : TangentSpace I (γ t) := (mfderiv (𝓡∂ 1) I γ t) 1
    let w : X := v
    calc ‖mfderiv I I p (γ t) v‖ₑ = ENNReal.ofReal ‖mfderiv I I p (γ t) v‖ := (ofReal_norm _).symm
         _ = ENNReal.ofReal ‖w‖ := congrArg ENNReal.ofReal (norm_push iso (γ t) w)
         _ = ‖w‖ₑ := ofReal_norm w
         _ = ‖v‖ₑ := (enorm_tangentSpace_vectorSpace (x:=γ t) (v:=v)).symm
  have down (a b : X) : edist (p a) (p b) ≤ edist a b := by
    rw [IsRiemannianManifold.out (I:=I) a b,riemannianEDist]
    refine le_iInf fun γ => le_iInf fun cg => ?_
    have bound : edist (p a) (p b) ≤ ∫⁻ t, ‖(mfderiv (𝓡∂ 1) I (p ∘ γ) t) 1‖ₑ := by
      rw [IsRiemannianManifold.out (I:=I),riemannianEDist]
      exact iInf_le_of_le (γ.map cov.continuous) (iInf_le _ (cp.comp cg))
    simpa only [energy γ cg] using bound
  intro x q
  let s := p ⁻¹' {q}
  have sc : IsClosed s := isClosed_singleton.preimage cov.continuous
  let γ := PathConnectedSpace.somePath (p x) q
  obtain ⟨f,fp,f0⟩ := cov.exists_path_lifts γ.toContinuousMap x γ.source
  have ne : s.Nonempty := ⟨f 1,(congrFun fp 1).trans γ.target⟩
  obtain ⟨y,hy,minimal⟩ := sc.exists_infDist_eq_dist ne x
  have py : p y=q := hy
  refine ⟨y,py,?_⟩
  apply (ENNReal.ofReal_eq_ofReal_iff dist_nonneg dist_nonneg).mp
  simp only [←edist_dist]
  apply le_antisymm _ (by simpa only [py] using down x y)
  rw [IsRiemannianManifold.out (I:=I) (p x) q,riemannianEDist]
  refine le_iInf fun path => le_iInf fun smooth => ?_
  obtain ⟨l,lp,l0⟩ := cov.exists_path_lifts path.toContinuousMap x path.source
  let η : Path x (l 1) := ⟨l,l0,rfl⟩
  have cm : ContMDiff (𝓡∂ 1) I 1 η := smooth_lift df smooth l.continuous lp
  have endpt : l 1∈s := (congrFun lp 1).trans path.target
  have near : dist x y ≤ dist x (l 1) := minimal ▸ Metric.infDist_le_dist_of_mem endpt
  have e : edist x (l 1) ≤ ∫⁻ t, ‖(mfderiv (𝓡∂ 1) I η t) 1‖ₑ := by
    rw [IsRiemannianManifold.out (I:=I),riemannianEDist]
    exact iInf_le_of_le η (iInf_le _ cm)
  apply ((by simpa only [edist_dist] using ENNReal.ofReal_le_ofReal near : edist x y ≤ edist x (l 1))).trans
  apply e.trans
  apply le_of_eq
  apply congrArg (fun f : unitInterval → ℝ≥0∞ => ∫⁻ t, f t)
  funext t
  have z := energy η cm t
  have eqp : (p ∘ η) = path := lp
  exact z.symm.trans (congrArg (fun h : unitInterval → Q => ‖(mfderiv (𝓡∂ 1) I h t) 1‖ₑ) eqp)
