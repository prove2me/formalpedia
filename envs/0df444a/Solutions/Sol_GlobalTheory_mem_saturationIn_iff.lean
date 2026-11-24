-- Prove2me | solution 1 for GlobalTheory.mem_saturationIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:27.680026+00:00
-- url     : https://prove2.me/submissions/fa232c54-fecd-42f0-a206-7e0b40c9130b

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
theorem _root_.solution [IsDomain R] {M N : Submodule R V} {x : V} :
    x ∈ saturationIn M N ↔ x ∈ M ∧ ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  rw [saturationIn_def, Submodule.mem_inf, mem_saturation_iff]
end GlobalTheory
