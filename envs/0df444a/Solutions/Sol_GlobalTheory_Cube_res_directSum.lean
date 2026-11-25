-- Prove2me | solution 1 for GlobalTheory.Cube.res_directSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:28.053468+00:00
-- url     : https://prove2.me/submissions/bfb6d349-26b4-4708-a664-a290487afa1d

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
theorem _root_.solution (A : κ → Cube.{v} ι R) {s t : Finset ι} (h : s ⊆ t) :
    Cube.res (Cube.directSum A) h = DirectSum.lmap fun k => Cube.res (A k) h := rfl
end Cube
end GlobalTheory
