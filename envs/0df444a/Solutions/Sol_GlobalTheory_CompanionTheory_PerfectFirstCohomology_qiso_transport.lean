-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomology.qiso_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:04:46.156207+00:00
-- url     : https://prove2.me/submissions/442431d2-3ce8-4716-ae9d-409f77ce9cc5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatQuotientOfUniversallyInjectiveStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LinearMapZeroOfInjectiveFullRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplittingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalSplittingKernelBaseChangeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelFreeAtPrimesOfConstantRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelBaseChangeTowerEquivStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RetractBaseChangeKernelCompatibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuasiIsomorphismDegreeOneKernelStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CochainBaseChangeEquivalencesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniversalCoefficientDegreeZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelEquivCohomologyOfQuasiIsomorphismStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyBaseChangeOfCochainEquivsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PerfectFirstCohomologyBaseChange

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfectFirstCohomology
namespace GlobalTheory.CompanionTheory.PerfectFirstCohomology
theorem _root_.solution {R S A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R] [CommRing S]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂'] [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module S A₀'] [Module S A₁'] [Module S A₂'] [Module S B₀'] [Module S B₁'] [Module S B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[S] A₁'} {a₁' : A₁' →ₗ[S] A₂'} {b₀' : B₀' →ₗ[S] B₁'} {b₁' : B₁' →ₗ[S] B₂'} {f' : A₁' →ₗ[S] B₁'}
    (h : QIsoAt a₀ a₁ b₀ b₁ f) (ε₀ : A₀ ≃+ A₀') (ε₁ : A₁ ≃+ A₁') (ε₂ : A₂ ≃+ A₂')
    (η₀ : B₀ ≃+ B₀') (η₁ : B₁ ≃+ B₁') (η₂ : B₂ ≃+ B₂')
    (h0 : ∀ y, a₀' (ε₀ y) = ε₁ (a₀ y)) (h1 : ∀ x, a₁' (ε₁ x) = ε₂ (a₁ x))
    (k0 : ∀ y, b₀' (η₀ y) = η₁ (b₀ y)) (k1 : ∀ x, b₁' (η₁ x) = η₂ (b₁ x))
    (hf : ∀ x, f' (ε₁ x) = η₁ (f x)) : QIsoAt a₀' a₁' b₀' b₁' f' := by
  unfold MainStatements.Hodge.QIsoAt at h ⊢
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun x' hx' ⟨y', hy'⟩ => ?_, fun z' hz' => ?_⟩
  · have ha : a₁ (ε₁.symm x') = 0 := by
      apply ε₂.injective
      rw [← h1, ε₁.apply_symm_apply, hx', map_zero]
    have hb : b₀ (η₀.symm y') = f (ε₁.symm x') := by
      apply η₁.injective
      rw [← k0, ← hf, η₀.apply_symm_apply, ε₁.apply_symm_apply, hy']
    obtain ⟨y, hy⟩ := hA _ ha ⟨_, hb⟩
    exact ⟨ε₀ y, by rw [h0, hy, ε₁.apply_symm_apply]⟩
  · have hz : b₁ (η₁.symm z') = 0 := by
      apply η₂.injective
      rw [← k1, η₁.apply_symm_apply, hz', map_zero]
    obtain ⟨x, y, hx, hxy⟩ := hB _ hz
    refine ⟨ε₁ x, η₀ y, by rw [h1, hx, map_zero], ?_⟩
    rw [hf, k0, ← hxy, map_sub, η₁.apply_symm_apply]
end GlobalTheory.CompanionTheory.PerfectFirstCohomology
