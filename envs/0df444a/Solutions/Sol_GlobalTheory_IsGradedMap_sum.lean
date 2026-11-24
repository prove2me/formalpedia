-- Prove2me | solution 1 for GlobalTheory.IsGradedMap.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:51.243333+00:00
-- url     : https://prove2.me/submissions/e3ea5e46-108c-4f8a-b3f4-e1903d3092bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
open GlobalTheory.IsGradedMap
variable {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {𝒬 : ℤ → Submodule R P}
namespace GlobalTheory.IsGradedMap
theorem _root_.solution {κ : Type*} (T : Finset κ) {f : κ → M →ₗ[MvPolynomial ι R] N}
    (hf : ∀ k ∈ T, IsGradedMap ℳ 𝒩 (f k)) : IsGradedMap ℳ 𝒩 (∑ k ∈ T, f k) := fun _ _ h => by
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun k hk => hf k hk h
end GlobalTheory.IsGradedMap
