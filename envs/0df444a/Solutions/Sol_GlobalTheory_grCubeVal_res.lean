-- Prove2me | solution 1 for GlobalTheory.grCubeVal_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:01.265968+00:00
-- url     : https://prove2.me/submissions/dea26901-b09c-4997-945e-43d05bdf56d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial DirectSum
open GlobalTheory
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] {n : ℤ}
namespace GlobalTheory
theorem _root_.solution {s t : Finset ι} (h : s ⊆ t) (z : (grCube ι ℳ n).obj s) :
    grCubeVal (Cube.res (grCube ι ℳ n) h z) = locRes X M h (grCubeVal z) := rfl
end GlobalTheory
