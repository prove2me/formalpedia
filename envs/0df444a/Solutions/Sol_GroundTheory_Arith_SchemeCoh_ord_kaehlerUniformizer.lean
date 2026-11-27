-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ord_kaehlerUniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:51.153028+00:00
-- url     : https://prove2.me/submissions/d76e7572-985e-4eab-9186-bee50846c2ea

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open GroundTheory.FunctionField KaehlerDifferential IntermediateField
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [IsFunctionField k K]
variable [PerfectField k]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (v : Place k K) : v.ord (kaehlerUniformizer v) = 1 :=
  (exists_ord_eq_one_D_ne_zero v).choose_spec.1
end GroundTheory.Arith.SchemeCoh
