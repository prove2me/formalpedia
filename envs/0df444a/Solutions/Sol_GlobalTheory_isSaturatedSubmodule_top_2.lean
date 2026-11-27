-- Prove2me | solution 2 for GlobalTheory.isSaturatedSubmodule_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:41:31.957162+00:00
-- url     : https://prove2.me/submissions/3a261714-1d2c-44c6-9248-dbdcdc72f696

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply

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
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
namespace GlobalTheory
theorem _root_.solution : IsSaturatedSubmodule (⊤ : Submodule R M) := by
  rw [isSaturatedSubmodule_iff_le]
  exact le_top
end GlobalTheory
