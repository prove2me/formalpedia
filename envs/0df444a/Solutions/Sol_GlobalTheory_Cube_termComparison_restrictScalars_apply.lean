-- Prove2me | solution 1 for GlobalTheory.Cube.termComparison_restrictScalars_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:39:14.32826+00:00
-- url     : https://prove2.me/submissions/7ba29638-221f-4ea9-bd4f-858e5da89d60

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
omit [LinearOrder ι]
namespace GlobalTheory
namespace Cube
theorem _root_.solution (A : Cube.{v} ι S) (p : ℕ) (x : Cube.Term A p)
    (s : {s : Finset ι // s.card = p}) :
    (Cube.termComparison (ModuleCat.restrictScalars f) A p).hom x s = x s := rfl
end Cube
end GlobalTheory
