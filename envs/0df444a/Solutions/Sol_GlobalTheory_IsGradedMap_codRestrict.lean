-- Prove2me | solution 1 for GlobalTheory.IsGradedMap.codRestrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:28.893992+00:00
-- url     : https://prove2.me/submissions/eb325db7-b9dd-46a0-945b-1382b4c61244

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
variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
omit [IsScalarTower R (MvPolynomial ι R) M]
namespace GlobalTheory
namespace IsGradedMap
theorem _root_.solution {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (K : Submodule (MvPolynomial ι R) N)
    (h : ∀ m, f m ∈ K) : IsGradedMap ℳ (grSub 𝒩 K) (f.codRestrict K h) := fun _ _ h => hf h
end IsGradedMap
end GlobalTheory
