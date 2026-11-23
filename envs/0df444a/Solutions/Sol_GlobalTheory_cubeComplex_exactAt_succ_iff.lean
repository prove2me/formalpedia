-- Prove2me | solution 1 for GlobalTheory.cubeComplex_exactAt_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:59.826319+00:00
-- url     : https://prove2.me/submissions/88bced5f-4d88-4b8a-b81a-c27daf9cd9ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex A).ExactAt (p + 1) ↔ Function.Exact (Cube.d A p) (Cube.d A (p + 1)) := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact ((cubeComplex A).d p (p + 1)) ((cubeComplex A).d (p + 1) (p + 1 + 1)) ↔ _
  rw [cubeComplex_d, cubeComplex_d]
  rfl
end GlobalTheory
