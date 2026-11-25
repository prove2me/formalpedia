-- Prove2me | solution 1 for GlobalTheory.dehomogenising_comp_of_saturating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:18:32.668347+00:00
-- url     : https://prove2.me/submissions/94dff649-8198-42d3-803e-7336c0bb09b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeCokerMatrixMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBaseChangeGrCubeIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsHomogeneousRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyHomLocSingletonEquivQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNoetherianSubringHomogeneousMatrixFlatChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FlatHomLocOfFlatHomLocSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FiniteGrCechHomology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DehomogenisingEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsGradedPresentationSaturating
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FiniteQuotSMulTopXSubOneOfChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DehomogenisingCompOfSaturating
import Theorems.Thm_GlobalTheory_IsGradedMap_comp
import Theorems.Thm_GlobalTheory_dehomogenising_eq_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum TensorProduct
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type}
    [CommRing R] {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩]
    [Decomposition 𝒩] {G : Type} [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    (𝒢 : ℤ → Submodule R G) {ψ : N →ₗ[MvPolynomial ι R] G} (hψ : IsGradedMap 𝒩 𝒢 ψ) (i : ι)
    (h₁ : ∀ y, ψ y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0)
    (h₂ : ∀ z : G, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ)
    {B : Type} [CommRing B] (π : MvPolynomial ι R →+* B) {P : Type} [AddCommGroup P] [Module B P]
    (ε : G →ₛₗ[π] P) (hπ : π (MvPolynomial.X i) = 1) (hε : Function.Surjective ε)
    (hk : ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    Function.Surjective (ε.comp ψ) ∧
      ∀ y, ε.comp ψ y = 0 ↔ ∃ w : N, y = (MvPolynomial.X i - 1 : MvPolynomial ι R) • w := by
  refine ⟨fun p => ?_, dehomogenising_eq_zero_iff ι R N 𝒩 i B π P (ε.comp ψ) hπ ?_⟩
  · obtain ⟨z, rfl⟩ := hε p
    obtain ⟨k, y, hy⟩ := h₂ z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, hy, LinearMap.map_smulₛₗ, map_pow, hπ, one_pow, one_smul]
  · intro n y hy h
    obtain ⟨k, hk⟩ := hk n _ (hψ hy) h
    obtain ⟨j, hj⟩ := h₁ _ ((map_smul ψ _ y).trans hk)
    exact ⟨j + k, by rw [pow_add, mul_smul, hj]⟩
end GlobalTheory
