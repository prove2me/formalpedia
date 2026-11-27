-- Prove2me | solution 1 for GlobalTheory.finrank_saturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:28.609728+00:00
-- url     : https://prove2.me/submissions/493a6243-d3f3-43c9-b1d4-f9ec6b8da875

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_rank_saturation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R M] (N : Submodule R M) :
    Module.finrank R (saturation N) = Module.finrank R N := congrArg Cardinal.toNat (rank_saturation N)
end GlobalTheory
