-- Prove2me | solution 1 for GlobalTheory.isIso_cechAugHomology_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:36.385301+00:00
-- url     : https://prove2.me/submissions/81cf43dc-2eb6-4691-8af0-8b1fbee41c86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
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
    IsIso (cechAugHomology A) ↔ (cubeComplex A).ExactAt 0 ∧ (cubeComplex A).ExactAt 1 := by
  rw [cechAugHomology, isIso_comp_right_iff, CochainComplex.isIso_liftCycles_iff, and_comm,
    cubeComplex_exactAt_zero_iff, cubeComplex_exactAt_one_iff,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, ModuleCat.mono_iff_injective]
  refine and_congr Iff.rfl ?_
  change Function.Exact (Cube.aug A) ((cechComplex A).d 0 (0 + 1)).hom ↔ _
  rw [cechComplex_d]
  rfl
end GlobalTheory
