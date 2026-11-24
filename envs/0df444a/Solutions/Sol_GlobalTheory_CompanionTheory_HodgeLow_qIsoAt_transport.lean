-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeLow.qIsoAt_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:27:05.664432+00:00
-- url     : https://prove2.me/submissions/f437712f-0428-4e84-8542-576b653005a7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow
namespace GlobalTheory.CompanionTheory.HodgeLow
theorem _root_.solution {R A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂']
    [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [Module R A₀'] [Module R A₁'] [Module R A₂'] [Module R B₀'] [Module R B₁'] [Module R B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[R] A₁'} {a₁' : A₁' →ₗ[R] A₂'} {b₀' : B₀' →ₗ[R] B₁'} {b₁' : B₁' →ₗ[R] B₂'}
    {f' : A₁' →ₗ[R] B₁'}
    (ea₀ : A₀ ≃ₗ[R] A₀') (ea₁ : A₁ ≃ₗ[R] A₁') (ea₂ : A₂ ≃ₗ[R] A₂')
    (eb₀ : B₀ ≃ₗ[R] B₀') (eb₁ : B₁ ≃ₗ[R] B₁') (eb₂ : B₂ ≃ₗ[R] B₂')
    (ha₀ : ∀ x, ea₁ (a₀ x) = a₀' (ea₀ x)) (ha₁ : ∀ x, ea₂ (a₁ x) = a₁' (ea₁ x))
    (hb₀ : ∀ x, eb₁ (b₀ x) = b₀' (eb₀ x)) (hb₁ : ∀ x, eb₂ (b₁ x) = b₁' (eb₁ x))
    (hf : ∀ x, eb₁ (f x) = f' (ea₁ x)) (h : QIsoAt a₀ a₁ b₀ b₁ f) :
    QIsoAt a₀' a₁' b₀' b₁' f' := by
  refine ⟨fun x' hx' ⟨y', hy'⟩ ↦ ?_, fun z' hz' ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := ea₁.surjective x'
    obtain ⟨y, rfl⟩ := eb₀.surjective y'
    have h1 : a₁ x = 0 := ea₂.injective (by rw [ha₁, hx', map_zero])
    have h2 : b₀ y = f x := eb₁.injective (by rw [hb₀, hy', hf])
    obtain ⟨w, rfl⟩ := h.1 x h1 ⟨y, h2⟩
    exact ⟨ea₀ w, (ha₀ w).symm⟩
  · obtain ⟨z, rfl⟩ := eb₁.surjective z'
    have h1 : b₁ z = 0 := eb₂.injective (by rw [hb₁, hz', map_zero])
    obtain ⟨x, y, hx, hy⟩ := h.2 z h1
    refine ⟨ea₁ x, eb₀ y, by rw [← ha₁, hx, map_zero], ?_⟩
    rw [← hf, ← map_sub, hy, hb₀]
end GlobalTheory.CompanionTheory.HodgeLow
