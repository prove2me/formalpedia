-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.inter_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:09.927832+00:00
-- url     : https://prove2.me/submissions/f418ea7d-5382-46e8-b83d-c6d010d28ebe

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
attribute [local semireducible] inter

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (U : ι → Opens X) {n : ℕ} (i : Fin n → ι) (a : Fin n) : inter U i ≤ U (i a) :=
  iInf_le (fun b => U (i b)) a
end GroundTheory.Arith.SchemeCoh
