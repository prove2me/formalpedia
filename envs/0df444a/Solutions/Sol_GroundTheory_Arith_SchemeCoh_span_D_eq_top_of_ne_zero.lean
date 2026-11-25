-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.span_D_eq_top_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:39.918441+00:00
-- url     : https://prove2.me/submissions/ea169235-6299-411d-b369-1af57f22fb4a

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_finrank_kaehlerDifferential

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
theorem _root_.solution {z : K} (hz : D k K z ≠ 0) :
    Submodule.span K {D k K z} = ⊤ :=
  have : FiniteDimensional K Ω[K⁄k] :=
    Module.finite_of_finrank_pos (by rw [finrank_kaehlerDifferential]; norm_num)
  Submodule.eq_top_of_finrank_eq (by
    rw [finrank_span_singleton hz, finrank_kaehlerDifferential])
end GroundTheory.Arith.SchemeCoh
