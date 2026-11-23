-- Prove2me | solution 1 for GlobalTheory.cechComplex_exactAt_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:38.523325+00:00
-- url     : https://prove2.me/submissions/f482e90e-073f-4842-99ac-51f38a46477b

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
    (cechComplex A).ExactAt (p + 1) ↔ Function.Exact (Cube.d A (p + 1)) (Cube.d A (p + 2)) := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact ((cechComplex A).d p (p + 1)) ((cechComplex A).d (p + 1) (p + 1 + 1)) ↔ _
  rw [cechComplex_d, cechComplex_d]
  rfl
end GlobalTheory
