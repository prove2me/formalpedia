-- Prove2me | solution 1 for NoHair.complete_flat_riemannian_euclidean_cover
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:56:31.989447+00:00
-- url     : https://prove2.me/submissions/043cd308-d91e-40b3-b447-14fc4152b4ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_complete_flat_euclidean_developing_projection
import Theorems.Thm_NoHair_euclidean_riemannian_cover_realizes_fiber_distance
import Theorems.Thm_NoHair_euclidean_riemannian_cover_deck_isometries_transitive
import Definitions.Def_NoHair_spatialRiemannCurvature

open NoHair Set Filter Bundle
open scoped Topology ContDiff Manifold

noncomputable section

theorem solution (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (flat : FlatInADMCharts Q) :
    ∃ p : ADMPoint → Q, IsCoveringMap p ∧
    IsLocalDiffeomorph 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ p ∧
    (∀ x v w : ADMPoint, inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x v)
      (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x w) = inner ℝ v w) ∧
    (∀ x : ADMPoint, ∀ q : Q, ∃ y : ADMPoint, p y=q ∧ dist x y=dist (p x) q) ∧
    ∀ x y, p x=p y → ∃ γ : ADMPoint ≃ᵢ ADMPoint, γ x=y ∧ ∀ z, p (γ z)=p z := by
  obtain ⟨p,cov,dif,iso⟩ := complete_flat_euclidean_developing_projection Q flat
  exact ⟨p,cov,dif,iso,euclidean_riemannian_cover_realizes_fiber_distance Q p cov dif iso,
    euclidean_riemannian_cover_deck_isometries_transitive Q p cov dif iso⟩
