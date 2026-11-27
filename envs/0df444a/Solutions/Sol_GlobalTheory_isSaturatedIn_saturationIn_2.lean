-- Prove2me | solution 2 for GlobalTheory.isSaturatedIn_saturationIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:08.022598+00:00
-- url     : https://prove2.me/submissions/b270ec5a-ed2f-4c46-a4db-7779389b8938

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
variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']
namespace GlobalTheory
theorem _root_.solution (M N : Submodule R V) : IsSaturatedIn M (saturationIn M N) := by
  unfold IsSaturatedIn
  rw [saturationIn_saturationIn]
end GlobalTheory
