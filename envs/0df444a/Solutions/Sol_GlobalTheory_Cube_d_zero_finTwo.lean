-- Prove2me | solution 1 for GlobalTheory.Cube.d_zero_finTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:38:49.270931+00:00
-- url     : https://prove2.me/submissions/052193b5-d0a5-4124-8b8a-d4c4d051fdd4

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
variable {R : Type u} [Ring R]
namespace GlobalTheory
namespace Cube
theorem _root_.solution (A : Cube.{v} (Fin 2) R) (x : Cube.Term A 0) :
    Cube.termOneFinTwo A (Cube.d A 0 x) =
      (Cube.res A (Finset.empty_subset _) (Cube.termZeroEquiv A x),
        Cube.res A (Finset.empty_subset _) (Cube.termZeroEquiv A x)) := by
  rw [Cube.d_zero_apply]
  rfl
end Cube
end GlobalTheory
