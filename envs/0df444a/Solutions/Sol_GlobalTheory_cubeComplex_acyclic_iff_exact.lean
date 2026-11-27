-- Prove2me | solution 1 for GlobalTheory.cubeComplex_acyclic_iff_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:41.515061+00:00
-- url     : https://prove2.me/submissions/aa274475-1cd2-482a-80a0-9100958e8646

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_isIso_cechAugHomology_iff
import Theorems.Thm_GlobalTheory_cubeComplex_acyclic_iff_cech
import Theorems.Thm_GlobalTheory_cechComplex_exactAt_succ_iff
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) :
    (cubeComplex A).Acyclic ↔ Function.Injective (Cube.aug A) ∧
      Function.Exact (Cube.aug A) (Cube.d A 1) ∧
        ∀ p, Function.Exact (Cube.d A (p + 1)) (Cube.d A (p + 2)) := by
  rw [cubeComplex_acyclic_iff_cech, isIso_cechAugHomology_iff, cubeComplex_exactAt_zero_iff,
    cubeComplex_exactAt_one_iff, and_assoc]
  simp only [← exactAt_iff_isZero_homology, cechComplex_exactAt_succ_iff]
end GlobalTheory
