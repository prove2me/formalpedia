-- Prove2me | solution 1 for GlobalTheory.Cube.d_restrictScalars_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:38:34.686666+00:00
-- url     : https://prove2.me/submissions/dc43d7de-df85-413b-ab7d-c4b9fc09226a

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] (f : R →+* S)
namespace GlobalTheory
namespace Cube
theorem _root_.solution (A : Cube.{v} ι S) (p : ℕ) (x : Cube.Term A p) :
    Cube.d (A ⋙ ModuleCat.restrictScalars f) p x = Cube.d A p x :=
  funext fun t => (Cube.d_apply (A ⋙ ModuleCat.restrictScalars f) p x t).trans
    (Cube.d_apply A p x t).symm
end Cube
end GlobalTheory
