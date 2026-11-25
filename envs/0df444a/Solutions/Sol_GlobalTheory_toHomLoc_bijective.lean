-- Prove2me | solution 1 for GlobalTheory.toHomLoc_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:36.021828+00:00
-- url     : https://prove2.me/submissions/0361ae0f-1a62-4a3b-b24f-597d32aca237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Theorems.Thm_GlobalTheory_awayFrac_zero_bijective
import Theorems.Thm_GlobalTheory_IsGradedMap_surjective_iff


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
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]
variable (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]
namespace GlobalTheory
theorem _root_.solution [Decomposition ℳ] {s : Finset ι}
    (h : Function.Bijective fun m : M => xProd R s • m) (n : ℤ) :
    Function.Bijective (toHomLoc ℳ s n) :=
  ⟨toHomLoc_injective ℳ h.1 n,
    (isGradedMap_awayFrac_zero ℳ s).surjective_iff.1 (awayFrac_zero_bijective h).2 n⟩
end GlobalTheory
