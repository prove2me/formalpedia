-- Prove2me | solution 1 for GlobalTheory.cechComplex_exactAt_succ_iff_cube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:28.118175+00:00
-- url     : https://prove2.me/submissions/b74a34ed-e43e-4a53-8abc-9f6f6f51d61f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_succ_iff
import Theorems.Thm_GlobalTheory_cechComplex_exactAt_succ_iff

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
    (cechComplex A).ExactAt (p + 1) ↔ (cubeComplex A).ExactAt (p + 2) := by
  rw [cechComplex_exactAt_succ_iff, cubeComplex_exactAt_succ_iff]
end GlobalTheory
