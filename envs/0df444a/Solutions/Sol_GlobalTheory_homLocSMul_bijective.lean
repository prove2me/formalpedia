-- Prove2me | solution 1 for GlobalTheory.homLocSMul_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:52.931467+00:00
-- url     : https://prove2.me/submissions/0d4e3a54-add3-43dd-834a-49583c583114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Theorems.Thm_GlobalTheory_smul_away_bijective
import Theorems.Thm_GlobalTheory_IsGradedMap_injective_iff
import Theorems.Thm_GlobalTheory_IsGradedMap_surjective_iff
import Theorems.Thm_GlobalTheory_isGradedMap_lsmul


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
theorem _root_.solution [Decomposition ℳ] {p : MvPolynomial ι R} {d : ℤ}
    (hp : p ∈ polyGrading ι R d) {s : Finset ι} {k : ℕ} (h : p ∣ xProd R s ^ k) (n : ℤ) :
    Function.Bijective (homLocSMul ℳ hp s n) :=
  ⟨(isGradedMap_lsmul (homLoc ℳ s) hp).injective_iff.1 (smul_away_bijective h).1 n,
    (isGradedMap_lsmul (homLoc ℳ s) hp).surjective_iff.1 (smul_away_bijective h).2 n⟩
end GlobalTheory
