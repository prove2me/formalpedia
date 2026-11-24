-- Prove2me | solution 1 for GlobalTheory.IsGradedMap.liftQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:31.641806+00:00
-- url     : https://prove2.me/submissions/d9e526dd-1a58-46e5-b12c-68f39e5ab466

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
omit [IsScalarTower R (MvPolynomial ι R) N]
namespace GlobalTheory
namespace IsGradedMap
theorem _root_.solution {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (K : Submodule (MvPolynomial ι R) M)
    (h : K ≤ LinearMap.ker f) : IsGradedMap (grQuot ℳ K) 𝒩 (K.liftQ f h) := by
  rintro n _ ⟨m, hm, rfl⟩
  exact hf hm
end IsGradedMap
end GlobalTheory
