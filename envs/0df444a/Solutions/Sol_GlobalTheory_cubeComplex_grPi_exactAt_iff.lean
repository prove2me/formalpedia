-- Prove2me | solution 1 for GlobalTheory.cubeComplex_grPi_exactAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:22.978608+00:00
-- url     : https://prove2.me/submissions/69135465-e346-4ef0-9593-a95bc44326be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Theorems.Thm_GlobalTheory_cubeComplex_directSum_exactAt_iff


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
variable {ι : Type} {R : Type u} [CommRing R] {κ : Type} [Fintype κ]
  {M : κ → Type u} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)] [∀ k, IsScalarTower R (MvPolynomial ι R) (M k)]
  (ℳ : ∀ k, ℤ → Submodule R (M k)) [∀ k, PolyGradedSMul ι (ℳ k)]
variable [LinearOrder ι]
variable [Finite ι]
namespace GlobalTheory
theorem _root_.solution (n : ℤ) (p : ℕ) :
    (cubeComplex (grCube ι (grPi ℳ) n)).ExactAt p ↔
      ∀ k, (cubeComplex (grCube ι (ℳ k) n)).ExactAt p :=
  (exactAt_iff_of_quasiIsoAt
    ((cubeFunctor ι R).mapIso (grCubePiIso ι ℳ n)).hom p).trans
    (cubeComplex_directSum_exactAt_iff _ p)
end GlobalTheory
