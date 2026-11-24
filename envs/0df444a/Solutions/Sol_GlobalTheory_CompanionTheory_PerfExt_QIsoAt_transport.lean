-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.QIsoAt.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:13.146322+00:00
-- url     : https://prove2.me/submissions/60aca686-e236-447d-a7b7-b9561df48011

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfExt
namespace GlobalTheory.CompanionTheory.PerfExt
namespace QIsoAt
theorem _root_.solution {R R' A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R] [CommRing R']
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂'] [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module R' A₀'] [Module R' A₁'] [Module R' A₂'] [Module R' B₀'] [Module R' B₁'] [Module R' B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[R'] A₁'} {a₁' : A₁' →ₗ[R'] A₂'} {b₀' : B₀' →ₗ[R'] B₁'} {b₁' : B₁' →ₗ[R'] B₂'} {f' : A₁' →ₗ[R'] B₁'}
    (u₁ : A₁ ≃+ A₁') (u₂ : A₂ ≃+ A₂') (v₁ : B₁ ≃+ B₁') (v₂ : B₂ ≃+ B₂')
    (h₁ : ∀ x, u₂ (a₁ x) = a₁' (u₁ x)) (h₂ : ∀ z, v₂ (b₁ z) = b₁' (v₁ z)) (hf : ∀ x, v₁ (f x) = f' (u₁ x))
    (ha : ∀ y, ∃ y', a₀' y' = u₁ (a₀ y)) (hb : ∀ y, ∃ y', b₀' y' = v₁ (b₀ y)) (hb' : ∀ y', ∃ y, v₁ (b₀ y) = b₀' y')
    (q : QIsoAt a₀ a₁ b₀ b₁ f) : QIsoAt a₀' a₁' b₀' b₁' f' := by
  obtain ⟨q₁, q₂⟩ := q
  refine ⟨fun x' hx ⟨y', hy⟩ ↦ ?_, fun z' hz ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := u₁.surjective x'
    obtain ⟨y, hy'⟩ := hb' y'
    obtain ⟨w, hw⟩ := q₁ x (u₂.injective (by rw [h₁, hx, map_zero]))
      ⟨y, v₁.injective (by rw [hy', hy, hf])⟩
    obtain ⟨w', hw'⟩ := ha w
    exact ⟨w', by rw [hw', hw]⟩
  · obtain ⟨z, rfl⟩ := v₁.surjective z'
    obtain ⟨x, y, hx, hy⟩ := q₂ z (v₂.injective (by rw [h₂, hz, map_zero]))
    obtain ⟨y', hy'⟩ := hb y
    exact ⟨u₁ x, y', by rw [← h₁, hx, map_zero], by rw [hy', ← hy, map_sub, hf]⟩
end QIsoAt
end GlobalTheory.CompanionTheory.PerfExt
