-- Prove2me | solution 1 for GlobalTheory.Cube.directSum_obj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:38:52.586945+00:00
-- url     : https://prove2.me/submissions/1d092d98-fa56-4059-b618-519a4f59250e

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
open DirectSum
variable {R : Type u} [Ring R] {κ : Type} [DecidableEq κ]
variable {ι : Type}
omit [DecidableEq κ]
namespace GlobalTheory
namespace Cube
theorem _root_.solution (A : κ → Cube.{v} ι R) (s : Finset ι) :
    (Cube.directSum A).obj s = ModuleCat.of R (⨁ k, (A k).obj s) := rfl
end Cube
end GlobalTheory
