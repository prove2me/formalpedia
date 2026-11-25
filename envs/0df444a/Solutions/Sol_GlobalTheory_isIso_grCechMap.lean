-- Prove2me | solution 1 for GlobalTheory.isIso_grCechMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:36.476932+00:00
-- url     : https://prove2.me/submissions/43f4a9c9-9cb2-44c8-9bcc-4de35783a442

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Theorems.Thm_GlobalTheory_homLocMap_bijective_of_X
import Theorems.Thm_GlobalTheory_isIso_cechComplexMap


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
namespace GlobalTheory
theorem _root_.solution [Decomposition ℳ] [Decomposition 𝒩] {f : M →ₗ[MvPolynomial ι R] N}
    (hf : IsGradedMap ℳ 𝒩 f)
    (h₁ : ∀ (i : ι) m, f m = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • m = 0)
    (h₂ : ∀ (i : ι) y, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ LinearMap.range f) (n : ℤ) :
    IsIso (grCechMap hf n) :=
  isIso_cechComplexMap _ fun _ ⟨i, hi⟩ => homLocMap_bijective_of_X hf hi (h₁ i) (h₂ i) n
end GlobalTheory
