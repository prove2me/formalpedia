-- Prove2me | solution 1 for GlobalTheory.cubeComplex_acyclic_iff_quasiIso_cechAug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:44.000816+00:00
-- url     : https://prove2.me/submissions/dd28a75c-df66-4f74-b2c4-d5ab75ed5121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_isIso_cechAugHomology_iff
import Theorems.Thm_GlobalTheory_cubeComplex_acyclic_iff_cech
import Theorems.Thm_GlobalTheory_quasiIsoAt_zero_cechAug_iff

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
    (cubeComplex A).Acyclic ↔ QuasiIso (cechAug A) := by
  rw [cubeComplex_acyclic_iff_cech, isIso_cechAugHomology_iff, ← quasiIsoAt_zero_cechAug_iff,
    quasiIso_iff]
  have h (p : ℕ) : QuasiIsoAt (cechAug A) (p + 1) ↔ IsZero ((cechComplex A).homology (p + 1)) := by
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ p),
      exactAt_iff_isZero_homology]
  refine ⟨fun H p => ?_, fun H => ⟨H 0, fun p => (h p).1 (H _)⟩⟩
  cases p with
  | zero => exact H.1
  | succ p => exact (h p).2 (H.2 p)
end GlobalTheory
