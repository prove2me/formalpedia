-- Prove2me | solution 1 for GlobalTheory.isSaturatedIn_iff_isTorsionFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:53.254175+00:00
-- url     : https://prove2.me/submissions/35c17612-0033-4fe7-8210-add2d604f454

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_isSaturatedIn_iff

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
variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']
namespace GlobalTheory
theorem _root_.solution [IsDomain R] {M N : Submodule R V} :
    IsSaturatedIn M N ↔ N ≤ M ∧ Module.IsTorsionFree R (M ⧸ N.submoduleOf M) := by
  rw [isSaturatedIn_iff, isSaturatedSubmodule_iff_isTorsionFree]
end GlobalTheory
