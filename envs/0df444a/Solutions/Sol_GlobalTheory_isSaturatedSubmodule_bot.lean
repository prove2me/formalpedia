-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:13.644877+00:00
-- url     : https://prove2.me/submissions/a7f0ba25-3515-4e10-91a4-8915a9a07f8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_isSaturatedSubmodule_bot_iff

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
theorem _root_.solution [IsDomain R] [Module.IsTorsionFree R M] :
    IsSaturatedSubmodule (⊥ : Submodule R M) := isSaturatedSubmodule_bot_iff.2 ‹_›
end GlobalTheory
