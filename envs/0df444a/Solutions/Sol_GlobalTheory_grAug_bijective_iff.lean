-- Prove2me | solution 1 for GlobalTheory.grAug_bijective_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:21.428587+00:00
-- url     : https://prove2.me/submissions/1b8f1587-45fd-4e2a-83c5-9529ac92cfe8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Theorems.Thm_GlobalTheory_isIso_cechAugHomology_iff


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
variable (ι : Type) {R : Type u} [CommRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type u} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]
variable {ι}
variable {ℳ}
variable [LinearOrder ι]
variable (ℳ)
namespace GlobalTheory
theorem _root_.solution (n : ℤ) : Function.Bijective (grAug ι ℳ n) ↔
    (cubeComplex (grCube ι ℳ n)).ExactAt 0 ∧ (cubeComplex (grCube ι ℳ n)).ExactAt 1 := by
  rw [← isIso_cechAugHomology_iff, ConcreteCategory.isIso_iff_bijective]
  exact Function.Bijective.of_comp_iff (cechAugHomology (grCube ι ℳ n)).hom
    (g := toHomLoc ℳ ∅ n) (homLocEmptyEquiv ι ℳ n).bijective
end GlobalTheory
