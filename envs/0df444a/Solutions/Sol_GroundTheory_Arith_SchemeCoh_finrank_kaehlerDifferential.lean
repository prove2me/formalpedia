-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.finrank_kaehlerDifferential
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:51.629701+00:00
-- url     : https://prove2.me/submissions/670820c8-b1fc-4a50-96fa-bd445f28bf71

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
variable (k K)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution : Module.finrank K Ω[K⁄k] = 1 := by
  obtain ⟨x, hx⟩ := exists_isSeparable_adjoin k K
  rw [← finrank_top, ← span_D_eq_top (k := k) x, finrank_span_singleton (D_ne_zero_of_isSeparable x)]
end GroundTheory.Arith.SchemeCoh
