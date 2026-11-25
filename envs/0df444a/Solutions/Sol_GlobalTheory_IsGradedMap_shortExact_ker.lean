-- Prove2me | solution 1 for GlobalTheory.IsGradedMap.shortExact_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:58.487664+00:00
-- url     : https://prove2.me/submissions/f5b17c5a-66ab-46c0-adc3-acf4cb5514b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Theorems.Thm_GlobalTheory_isGradedMap_subtype


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial CategoryTheory
universe u
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) P]
omit [IsScalarTower R (MvPolynomial ι R) P]
namespace GlobalTheory
namespace IsGradedMap
theorem _root_.solution {𝒩 : ℤ → Submodule R N} {𝒬 : ℤ → Submodule R P}
    {g : N →ₗ[MvPolynomial ι R] P} (hg : IsGradedMap 𝒩 𝒬 g) (h : Function.Surjective g) :
    GradedShortExact (grSub 𝒩 (LinearMap.ker g)) 𝒩 𝒬 (LinearMap.ker g).subtype g :=
  ⟨isGradedMap_subtype _ _, hg, Submodule.injective_subtype _, LinearMap.exact_subtype_ker_map g, h⟩
end IsGradedMap
end GlobalTheory
