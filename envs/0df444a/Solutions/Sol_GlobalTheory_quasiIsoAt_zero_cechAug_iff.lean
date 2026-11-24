-- Prove2me | solution 1 for GlobalTheory.quasiIsoAt_zero_cechAug_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:40.679527+00:00
-- url     : https://prove2.me/submissions/af734f22-5856-44c6-8934-aa968a4d0f53

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
    QuasiIsoAt (cechAug A) 0 ↔ (cubeComplex A).ExactAt 0 ∧ (cubeComplex A).ExactAt 1 := by
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros _ rfl rfl rfl, and_comm,
    cubeComplex_exactAt_zero_iff, cubeComplex_exactAt_one_iff,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, ModuleCat.mono_iff_injective]
  change Function.Injective ((cechAug A).f 0).hom ∧
    Function.Exact ((cechAug A).f 0).hom ((cechComplex A).d 0 (0 + 1)).hom ↔ _
  rw [cechComplex_d, cechAug_f_zero]
  rfl
end GlobalTheory
